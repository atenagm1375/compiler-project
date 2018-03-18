/*
 *  The scanner definition for COOL.
 */

/*
 *  Stuff enclosed in %{ %} in the first section is copied verbatim to the
 *  output, so headers and global definitions are placed here to be visible
 * to the code in the file.  Don't remove anything that was here initially
 */
%{
#include <cool-parse.h>
#include <stringtab.h>
#include <utilities.h>

/* The compiler assumes these identifiers. */
#define yylval cool_yylval
#define yylex  cool_yylex

/* Max size of string constants */
#define MAX_STR_CONST 1025
#define YY_NO_UNPUT   /* keep g++ happy */

extern FILE *fin; /* we read from this file */

/* define YY_INPUT so we read from the FILE fin:
 * This change makes it possible to use this scanner in
 * the Cool compiler.
 */
#undef YY_INPUT
#define YY_INPUT(buf,result,max_size) \
	if ( (result = fread( (char*)buf, sizeof(char), max_size, fin)) < 0) \
		YY_FATAL_ERROR( "read() in flex scanner failed");

char string_buf[MAX_STR_CONST]; /* to assemble string constants */
char *string_buf_ptr;

extern int curr_lineno;
extern int verbose_flag;

extern YYSTYPE cool_yylval;

/*
 *  Add Your own definitions here
 */

 int nested_comments_count = 0;
 int lenstr = 0;

bool invalidSize();
int strLengthError();

%}

/*
 * Define names for regular expressions here.
 */

DARROW          =>
DIGIT           [0-9]
UPPERCASE       [A-Z]
LOWERCASE       [a-z]
ALPHANUMERIC    [a-zA-z0-9_]
WHITESPACE      [ \t\r\v\f]

%x COMMENT
%x STRING
%x WRONGSTRING

%%

 /*
  *  Nested comments
  */
<INITIAL,COMMENT>"(*" {
		nested_comments_count++;
		BEGIN(COMMENT);
}

<COMMENT>\n {
		curr_lineno++;
}

<COMMENT>. {}

<COMMENT>"*)" {
		nested_comments_count--;
		if (nested_comments_count == 0){
			BEGIN(INITIAL);
		}
}

<COMMENT><<EOF>> {
		BEGIN(INITIAL);
		cool_yylval.error_msg = "EOF in comment";
		return(ERROR);
}

<INITIAL>"*)" {
		cool_yylval.error_msg = "Unmatched *)";
		return(ERROR);
}

 /*
  *  The single-line comment.
  */
"--".*\n {
		curr_lineno++;
}

"--".* {
		curr_lineno++;
}

 /*
  *  The multiple-character operators.
  */
{DARROW}		{ return (DARROW); }

"<-" {
		return(ASSIGN);
}

"<=" {
		return(LE);
}

 /*
  *  The single-character operators.
  */
"=" {
		return('=');
}

"<" {
		return('<');
}

"{" {
		return('{');
}

"}" {
		return('}');
}

"(" {
		return('(');
}

")" {
		return(')');
}

"+" {
		return('+');
}

"-" {
		return('-');
}

"*" {
		return('*');
}

"/" {
		return('/');
}

"." {
		return('.');
}

"~" {
		return('~');
}

"@" {
		return('@');
}

";" {
		return(';');
}

":" {
		return(':');
}

"," {
		return(',');
}

 /*
  * Keywords are case-insensitive except for the values true and false,
  * which must begin with a lower-case letter.
  */
t(?i:rue) {
		cool_yylval.boolean = true;
		return(BOOL_CONST);
}

f(?i:alse) {
		cool_yylval.boolean = false;
		return(BOOL_CONST);
}

(?i:class) {
		return(CLASS);
}

(?i:inherits) {
		return(INHERITS);
}

(?i:if) {
		return(IF);
}

(?i:then) {
		return(THEN);
}

(?i:else) {
		return(ELSE);
}

(?i:fi) {
		return(FI);
}

(?i:while) {
		return(WHILE);
}

(?i:loop) {
		return(LOOP);
}

(?i:pool) {
		return(POOL);
}

(?i:case) {
		return(CASE);
}

(?i:of) {
		return(OF);
}

(?i:esac) {
		return(ESAC);
}

(?i:new) {
		return(NEW);
}

(?i:let) {
		return(LET);
}

(?i:in) {
		return(IN);
}

(?i:isvoid) {
		return(ISVOID);
}

(?i:not) {
		return(NOT);
}

{UPPERCASE}{ALPHANUMERIC}* {
		cool_yylval.symbol = idtable.add_string(yytext);
		return(TYPEID);
}

{LOWERCASE}{ALPHANUMERIC}* {
		cool_yylval.symbol = idtable.add_string(yytext);
		return(OBJECTID);
}

{DIGIT}+ {
		cool_yylval.symbol = inttable.add_string(yytext);
		return(INT_CONST);
}

 /*
  *  String constants (C syntax)
  *  Escape sequence \c is accepted for all characters c. Except for
  *  \n \t \b \f, the result is c.
  *
  */
\" {
		BEGIN(STRING);
}

<STRING>\" {
		cool_yylval.symbol = stringtable.add_string(string_buf);
		lenstr = 0;
		string_buf[0] = '\0';
		BEGIN(INITIAL);
		return(STR_CONST);
}

<STRING>(\0|\\\0) {
        cool_yylval.error_msg = "String contains null character";
		BEGIN(WRONGSTRING);
		return(ERROR);
}

<WRONGSTRING>.*[\"\n] {
		BEGIN(INITIAL);
}

<STRING>\\\n {
		if (invalidSize()) {
			return(strLengthError());
		}
		curr_lineno++;
		strcat(string_buf, "\n");
		lenstr++;
}

<STRING>\n {
		curr_lineno++;
		BEGIN(INITIAL);
		lenstr = 0;
		string_buf[0] = '\0';
		cool_yylval.error_msg = "Unterminated string constant";
		return(ERROR);
}

<STRING><<EOF>> {
		BEGIN(INITIAL);
		cool_yylval.error_msg = "EOF in string constant";
		return(ERROR);
}

<STRING>\\n {
		if (invalidSize()) {
			return(strLengthError());
		}
		curr_lineno++;
		strcat(string_buf, "\n");
}

<STRING>\\b {
		if (invalidSize()) {
			return(strLengthError());
		}
		lenstr++;
		strcat(string_buf, "\b");
}

<STRING>\\t {
		if (invalidSize()) {
			return(strLengthError());
		}
		lenstr++;
		strcat(string_buf, "\t");
}

<STRING>\\. {
		if (invalidSize()) {
			return(strLengthError());
		}
		lenstr++;
		strcat(string_buf, &strdup(yytext)[1]);
}

<STRING>. {
		if (invalidSize()) {
			return(strLengthError());
		}
		lenstr++;
		strcat(string_buf, yytext);
}

\n {
		curr_lineno++;
}

{WHITESPACE} {}

. {
		yylval.error_msg = yytext;
		return(ERROR);
}

%%

/* =========================================================== */

bool invalidSize() {
	if (lenstr + 1 >= MAX_STR_CONST) {
		BEGIN(WRONGSTRING);
		return(true);
	}
	return(false);
}

int strLengthError() {
	lenstr = 0;
	string_buf[0] = '\0';
	cool_yylval.error_msg = "String constant too long";
	return(ERROR);
}
