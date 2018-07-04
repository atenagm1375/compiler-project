

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"


extern int semant_debug;
extern char *curr_filename;

symtable_type *class_table;
symtable_type *var_table;
method_table_type *method_table;
ClassTable *table;

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////
static Symbol
    arg,
    arg2,
    Bool,
    concat,
    cool_abort,
    copy,
    Int,
    in_int,
    in_string,
    IO,
    length,
    Main,
    main_meth,
    No_class,
    No_type,
    Object,
    out_int,
    out_string,
    prim_slot,
    self,
    SELF_TYPE,
    Str,
    str_field,
    substr,
    type_name,
    val;
//
// Initializing the predefined symbols.
//
static void initialize_constants(void)
{
    arg         = idtable.add_string("arg");
    arg2        = idtable.add_string("arg2");
    Bool        = idtable.add_string("Bool");
    concat      = idtable.add_string("concat");
    cool_abort  = idtable.add_string("abort");
    copy        = idtable.add_string("copy");
    Int         = idtable.add_string("Int");
    in_int      = idtable.add_string("in_int");
    in_string   = idtable.add_string("in_string");
    IO          = idtable.add_string("IO");
    length      = idtable.add_string("length");
    Main        = idtable.add_string("Main");
    main_meth   = idtable.add_string("main");
    //   _no_class is a symbol that can't be the name of any
    //   user-defined class.
    No_class    = idtable.add_string("_no_class");
    No_type     = idtable.add_string("_no_type");
    Object      = idtable.add_string("Object");
    out_int     = idtable.add_string("out_int");
    out_string  = idtable.add_string("out_string");
    prim_slot   = idtable.add_string("_prim_slot");
    self        = idtable.add_string("self");
    SELF_TYPE   = idtable.add_string("SELF_TYPE");
    Str         = idtable.add_string("String");
    str_field   = idtable.add_string("_str_field");
    substr      = idtable.add_string("substr");
    type_name   = idtable.add_string("type_name");
    val         = idtable.add_string("_val");
}

Type Null_type = NULL;
Type Self_type = NULL;
Type Int_type = NULL;
Type String_type = NULL;
Type IO_type = NULL;
Type Bool_type = NULL;
Type Object_type = NULL;
Type current_type = NULL;

Symbol filename;

Type lookup_install_type(Symbol name, Class_ class_=NULL, Type parent_type=NULL) {
    class_tree_node type = class_table->lookup(name);
    if (!type) {
        type = new class_tree_node_type(name);
        class_table->addid(name, type);
    }
    if (class_) {
        if (type->is_defined()) {
            table->semant_error() << "Overriding existing class " << name << endl;
        }
        type->set_contain(class_);
    }
    if (parent_type) {
        type->set_parent(parent_type);
    }
    return type;
}

class_tree_node union_set(class_tree_node first, class_tree_node second) {
	first = first->find_set();
	second = second->find_set();
	if (first == second) {
		return NULL;
	}

	class_tree_node new_root = (first->rank < second->rank) ? second : first;
	new_root->size = first->size + second->size;
	new_root->rank += (first->rank == second->rank);
	first->head = second->head = new_root;

	return new_root;
}

Type::Type(class_tree_node n) : node(n ? n : Null_type.node) { }

Type::operator bool() const {
    return node && node != Null_type.node && node->is_defined();
}

bool operator ==(const Type &a, class_tree_node b) { return a.node == b; }

bool operator!=(const Type &a, class_tree_node b) { return !(a == b); }

bool operator==(class_tree_node a, const Type &b) { return a == b.node; }

bool operator!=(class_tree_node a, const Type &b) { return !(a == b); }

bool operator==(const Type &a, const Type &b) { return a.node == b.node; }

bool operator!=(const Type &a, const Type &b) { return !(a == b); }

bool operator==(const Expression &e, const Type &t) { return e->get_Expr_Type() == t; }

bool operator!=(const Expression &e, const Type &t) { return !(e == t); }

bool operator<=(const Type &a, const Type &b) {
	if (b == Self_type) {
		return a == Self_type;
	}
	return (a == Self_type ? current_type : a)->is_sub_class_of(b);
}

Type lca_assist(class_tree_node t1, class_tree_node t2) {
    if (!t1 || !t2) {
        return NULL;
    }
    int depth = (t1->depth < t2->depth) ? t1->depth : t2->depth;
    while(t1 && t1->depth != depth) {
        t1 = t1->parent;
    }
    while(t2 && t2->depth != depth) {
        t2 = t2->parent;
    }

    while(t1 && t2 && t1 != t2) {
        t1 = t1->parent;
        t2 = t2->parent;
    }
    return (t1) ? t2 : NULL;
}

Type find_type_lca(const Type &T1, const Type &T2) {
    Type t1 = (T1 == Self_type) ? current_type : T1;
    Type t2 = (T2 == Self_type) ? current_type : T2;
    return lca_assist(t1, t2);
}

bool class_method_type::is_same_method(class_method t) const {
	if (!t || t->type != type) {
		return false;
	}
	return next ? next->is_same_method( t->next) : true;
}

ClassTable::ClassTable(Classes classes) : semant_errors(0) , error_stream(cerr) {
    table = this;
    class_table = &symtable;
    var_table = &vartable;
    class_table->enterscope();
    install_basic_classes();
    class_tree_node root = class_table->probe(Object);

    if (!root) {
        semant_error() << "Could not find Object class" << endl;
        return;
    }

    int counter = root->find_set()->size;
    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        Class_ current_class = classes->nth(i);

        class_tree_node cur_node = lookup_install_type(current_class->get_name());
        if (cur_node->contain == NULL) {
            cur_node->set_contain(current_class);
        } else {
            semant_error(current_class) << "Redefinition of Class " << current_class->get_name() << endl;
            return;
        }

        class_tree_node par_node = lookup_install_type(current_class->get_parent_name());
        if (par_node == cur_node) {
            semant_error(current_class) << "Class " << current_class->get_name() << " Cannot inherit from itself"
                << endl;
        }
        if (par_node == Int_type || par_node == Bool_type || par_node == String_type) {
            semant_error(current_class) << "Cannot inherit from " << current_class->get_parent_name() << endl;
        }
        if (par_node == Self_type) {
            semant_error(current_class) << "Cannot inherit from SELF_TYPE" << endl;
            par_node = Object_type;
        }
        if (!cur_node->set_parent(par_node)) {
            semant_error(current_class) << "Class " << current_class->get_name() << " cannot inherit from "
                << current_class->get_parent_name() << endl;
            return;
        }
        counter++;
    }

    class_tree_node_type::fill_node_depth();

    root->walk_down();
    if (!class_table->lookup(Main)) {
		semant_error() << "Class Main is not defined." << endl;
	}
    class_table->exitscope();
}

void ClassTable::install_basic_classes() {

    // The tree package uses these globals to annotate the classes built below.
   // curr_lineno  = 0;
    Symbol filename = stringtable.add_string("<basic class>");

    // The following demonstrates how to create dummy parse trees to
    // refer to basic Cool classes.  There's no need for method
    // bodies -- these are already built into the runtime system.

    // IMPORTANT: The results of the following expressions are
    // stored in local variables.  You will want to do something
    // with those variables at the end of this method to make this
    // code meaningful.

    //
    // The Object class has no parent class. Its methods are
    //        abort() : Object    aborts the program
    //        type_name() : Str   returns a string representation of class name
    //        copy() : SELF_TYPE  returns a copy of the object
    //
    // There is no need for method bodies in the basic classes---these
    // are already built in to the runtime system.

    Class_ Object_class =
	class_(Object,
	       No_class,
	       append_Features(
			       append_Features(
					       single_Features(method(cool_abort, nil_Formals(), Object, no_expr())),
					       single_Features(method(type_name, nil_Formals(), Str, no_expr()))),
			       single_Features(method(copy, nil_Formals(), SELF_TYPE, no_expr()))),
	       filename);

    //
    // The IO class inherits from Object. Its methods are
    //        out_string(Str) : SELF_TYPE       writes a string to the output
    //        out_int(Int) : SELF_TYPE            "    an int    "  "     "
    //        in_string() : Str                 reads a string from the input
    //        in_int() : Int                      "   an int     "  "     "
    //
    Class_ IO_class =
	class_(IO,
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       single_Features(method(out_string, single_Formals(formal(arg, Str)),
										      SELF_TYPE, no_expr())),
							       single_Features(method(out_int, single_Formals(formal(arg, Int)),
										      SELF_TYPE, no_expr()))),
					       single_Features(method(in_string, nil_Formals(), Str, no_expr()))),
			       single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
	       filename);

    //
    // The Int class has no methods and only a single attribute, the
    // "val" for the integer.
    //
    Class_ Int_class =
	class_(Int,
	       Object,
	       single_Features(attr(val, prim_slot, no_expr())),
	       filename);

    //
    // Bool also has only the "val" slot.
    //
    Class_ Bool_class =
	class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),filename);

    //
    // The class Str has a number of slots and operations:
    //       val                                  the length of the string
    //       str_field                            the string itself
    //       length() : Int                       returns length of the string
    //       concat(arg: Str) : Str               performs string concatenation
    //       substr(arg: Int, arg2: Int): Str     substring selection
    //
    Class_ Str_class =
	class_(Str,
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       append_Features(
									       single_Features(attr(val, Int, no_expr())),
									       single_Features(attr(str_field, prim_slot, no_expr()))),
							       single_Features(method(length, nil_Formals(), Int, no_expr()))),
					       single_Features(method(concat,
								      single_Formals(formal(arg, Str)),
								      Str,
								      no_expr()))),
			       single_Features(method(substr,
						      append_Formals(single_Formals(formal(arg, Int)),
								     single_Formals(formal(arg2, Int))),
						      Str,
						      no_expr()))),
	       filename);

    Class_ No_class = class_(No_type, Object, nil_Features(), filename);
    Class_ Self_class = class_(SELF_TYPE, Object, nil_Features(), filename);

    ::Null_type = lookup_install_type(No_type, No_class);
    ::Self_type = lookup_install_type(SELF_TYPE, Self_class);
    ::Object_type = lookup_install_type(Object, Object_class);
    ::Int_type = lookup_install_type(Int, Int_class, Object_type);
    ::Bool_type = lookup_install_type(Bool, Bool_class, Object_type);
    ::String_type = lookup_install_type(Str, Str_class, Object_type);
    ::IO_type = lookup_install_type(IO, IO_class, Object_type);

    lookup_install_type(prim_slot, No_class);
}

////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////

ostream& ClassTable::semant_error(Class_ c) {
    return semant_error(c->get_filename(),c);
}

ostream& ClassTable::semant_error(Symbol filename, tree_node *t) {
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

ostream& ClassTable::semant_error() {
    semant_errors++;
    return error_stream;
}



ostream& semant_error(Class_ c) {
    return table->semant_error(c->get_filename(), c);
}

ostream& semant_error(tree_node *t) {
    return table->semant_error(current_type->contain->get_filename(), t);
}

ostream& semant_error(Symbol filename, tree_node *t) {
    return table->semant_error(filename, t);
}

ostream& semant_error() {
    return table->semant_error();
}


class_tree_node class_tree_node_type::nodes_head = NULL;

bool class_tree_node_type::is_defined() const {
	return contain && this != Null_type;
}

bool class_tree_node_type::fill_depth() {
    if (depth == -1) {
        if (parent) {
            if (!parent->fill_depth()) {
                semant_error(this->contain) << "Class " << name << " inherits from undefined class "
                    << parent->name << endl;
            }
            depth = parent->depth + 1;
        }
        else {
            depth = 0;
        }
        find_set();
    }
    return this->contain;
}

bool class_tree_node_type::walk_down() {
    ::current_type = this;
    ::filename = contain->get_filename();

    var_table->enterscope();
    var_table->addid(self, Self_type);
    if (is_defined()) {
        this->contain->check_Class_Types();
    }

    bool ret = true;
    class_tree_node ch = this->child;
    while (ch) {
        ret &= ch->walk_down();
        ch = ch->sibiling;
    }
    var_table->exitscope();
    return ret;
}


/*   This is the entry point to the semantic checker.

     Your checker should do the following two things:

     1) Check that the program is semantically correct
     2) Decorate the abstract syntax tree with type information
        by setting the `type' field in each Expression node.
        (see `tree.h')

     You are free to first do 1), make sure you catch all semantic
     errors. Part 2) can be done in a second stage, when you want
     to build mycoolc.
 */
void program_class::semant()
{
    initialize_constants();

    /* ClassTable constructor may do some semantic analysis */
    ClassTable *classtable = new ClassTable(classes);

    /* some semantic analysis code may go here */

    if (classtable->errors()) {
	cerr << "Compilation halted due to static semantic errors." << endl;
	exit(1);
    }
}


Type check_dispatch(Type T0, Type T, Symbol name, Expressions actual, Expression e) {
    class_method types = T->find_method(name);
	if (!types) {
		semant_error(filename, e) << "Call on method " << name << " on Class " << T->name
            << " failed." << endl;
		semant_error(filename, e) << "\tCould not find method." << endl;
		return Null_type;
	}

	Type ret_type = types->hd();
	ret_type = ret_type == Self_type ? T0 : ret_type;

	types = types->tl();

	int i = actual->first();
	while (actual->more( i) && types) {
		Expression expr = actual->nth( i);
		Type act_type = expr->get_Expr_Type();
		Type para_type = types->hd();
		act_type = act_type == Self_type ? current_type : act_type;
		if (act_type && para_type && act_type.is_sub_type_of( para_type)) {
			types = types->tl(), i = actual->next( i);
		} else {
			break;
		}
	}
	if (actual->more( i) || types) {
		char *err_str;
		if (!actual->more( i)) {
			err_str = "Too few arguments supplied";
		} else {
			if(types) {
				err_str = "Arguments miss match";
			} else {
				err_str = "Too many arguments supplied";
			}
		}

		semant_error(filename, e) << "Calls on method " << name << " on Class " << T->name << " failed." << endl;
		semant_error(filename, e) << "\t" << err_str << endl;
	}

    return ret_type;
}


Type arithmetic_type_check(Expression e1, Expression e2, Expression e, char *op) {
    if (e1->get_Expr_Type() != Int_type) {
        semant_error(filename, e) << "Left operand of " << op << " should be Int" << endl;
    }
    if (e2->get_Expr_Type() != Int_type) {
        semant_error(filename, e) << "Right operand of " << op << " should be Int" << endl;
    }
    return Int_type;
}


Type Expression_class::get_Expr_Type() {
    if (!checked) {
        expr_type = do_Check_Expr_Type();
        if (expr_type) {
            set_type(expr_type->name);
        } else {
            set_type(NULL);
        }
        checked = true;
    }
    return expr_type;
}


void class__class::collect_Methods() {
    for (int i = features->first(); features->more(i); i = features->next(i)) {
        features->nth(i)->collect_Feature_Types();
    }
}


bool class__class::check_Class_Types() {
    for (int i = features->first(); features->more(i); i = features->next(i)) {
        features->nth(i)->install_Feature_Types();
    }

    for (int i = features->first(); features->more(i); i = features->next(i)) {
        Feature f = features->nth(i);
        if (!f->check_Feature_Types()) { continue; }
    }
    return true;
}


void method_class::collect_Feature_Types() {
    feature_type = lookup_install_type(return_type);
	class_method syms = new class_method_type( feature_type);
	class_method last = syms;
	for (int i = formals->first(); formals->more(i); i = formals->next(i)) {
		Type type = formals->nth(i)->collect_Formal_Type();
		class_method cur = new class_method_type(type);
		last->set_tl(cur);
		last = cur;
	}
    method_table->addid( name, syms);
}


bool method_class::install_Feature_Types() { return true; }


bool method_class::check_Feature_Types() {
    if (current_type->parent) {
		class_method last = current_type->parent->find_method(name);
		class_method syms = current_type->find_method(name);
		if (last && !syms->is_same_method(last)) {
			semant_error(filename, this) << "Signature changed for method " << name << endl;
		}
	}

	var_table->enterscope();
	for (int i = formals->first(); formals->more(i); i = formals->next(i)) {
		Formal fm = formals->nth(i);
		if (fm->check_Formal_Type()) {
			fm->install_Formal_Type();
		}
	}

	Type type = feature_type;
	Type body_type = expr->get_Expr_Type();
	var_table->exitscope();

	if (type) {
		if (!body_type) {
			body_type = type;
		}
		if (!body_type.is_sub_type_of( type)) {
			semant_error(filename, this) << "In Class " << current_type->name << ", return type of method "
            << this->name << " which is not a subtype of class " << type->name << endl;
		}
	} else {
		semant_error(filename, this) << "In Class " << current_type->name << ", return type of method " << this->name
		       << ", Class " << type->name << " is not defined." << endl;
	}
    return type && body_type && body_type.is_sub_type_of(type);
}


void attr_class::collect_Feature_Types() { }


bool attr_class::install_Feature_Types() {
    feature_type = lookup_install_type(type_decl);
    if (var_table->probe(name)) {
        semant_error(filename, this) << "Attribute " << name << " already exists" << endl;
    } else if(var_table->lookup(name)) {
        semant_error(filename, this) << "Attribute " << name << " is an attribute of inherited class" << endl;
    } else {
        var_table->addid(name, feature_type);
        return true;
    }
    return false;
}


bool attr_class::check_Feature_Types() {
    Type T = feature_type;
    Type T1 = init->is_no_expr() ? T : init->get_Expr_Type();
    if (!T) {
        semant_error(filename, this) << "Class " << type_decl << " is not defined" << endl;
    } else if (T1 && !T1.is_sub_type_of(T)) {
        semant_error(filename, this) << "Could not initialize attribute " << name << " of class "
            << type_decl << " with class " << T1->name << endl;
    } else if (!T1) {
        T1 = T;
    }
    return T1;
}


Type formal_class::collect_Formal_Type() {
    ext_type = lookup_install_type(type_decl);
    return ext_type;
}


bool formal_class::check_Formal_Type() {
    if (!ext_type) {
        semant_error(filename, this) << "Class " << this->type_decl << " is not defined" << endl;
    }
    if (var_table->probe(name)) {
        semant_error(filename, this) << "Formal parameter " << this->name << " already exists" << endl;
    }
    if (name == self) {
        semant_error(filename, this) << "Invalid use of self in formal parameters" << endl;
    }
    if (ext_type == Self_type) {
        semant_error(filename, this) << "SELF_TYPE could not be a formal type" << endl;
    }
    return ext_type && !var_table->probe(name) && name != self && ext_type != Self_type;
}


void formal_class::install_Formal_Type() {
    var_table->addid(name, ext_type);
}


bool branch_class::install_Case_Type() {
    id_type = class_table->lookup(type_decl);
    if (class_table->probe(type_decl)) {
        semant_error(filename, this) << "Case already exists" << endl;
        return false;
    }
    if (id_type) {
        class_table->addid(type_decl, id_type);
    }
    return true;
}


Type branch_class::check_Case_Type(Type path_type) {
    Type T = Null_type;
    if (!id_type) {
        semant_error(filename, this) << "Class " << type_decl << " is not defined" << endl;
    } else {
        var_table->enterscope();
        var_table->addid(name, id_type);
        T = expr->get_Expr_Type();
        var_table->exitscope();
    }
    return T ? T : path_type;
}


Type assign_class::do_Check_Expr_Type() {
    if (name == self) {
        semant_error(filename, this) << "Assignment on self object" << endl;
    }
    Type T1 = var_table->lookup(name);
    Type T2 = expr->get_Expr_Type();
    if (!T1) {
        semant_error(filename, this) << "Variable " << name << " is not defined" << endl;
    } else if (T2 && !T2.is_sub_type_of(T1)) {
        semant_error(filename, this) << "Invalid assignment of class " << T1->name << " to class " << T2->name << endl;
    }
    return T2;
}


Type static_dispatch_class::do_Check_Expr_Type() {
    Type T0 = expr->get_Expr_Type();
    Type T = class_table->lookup(type_name);
    if (!T) {
        semant_error(filename, this) << "Class " << type_name << " is not defined" << endl;
        return Null_type;
    }
    if (T0 && !T0.is_sub_type_of(T)) {
        semant_error(filename, this) << "Could not convert class " << T0->name << " to class " << type_name << endl;
        return Null_type;
    }
    return check_dispatch(T0, T, name, actual, this);
}


Type dispatch_class::do_Check_Expr_Type() {
    Type T0 = expr->get_Expr_Type();
    if (!T0) {
        return Null_type;
    }
    Type T = (T0 == Self_type) ? current_type : T0;
    return check_dispatch(T0, T, name, actual, this);
}


Type cond_class::do_Check_Expr_Type() {
    if (pred->get_Expr_Type() != Bool_type) {
        semant_error(filename, this) << "Condition expression should be Bool" << endl;
    }
    Type T1 = then_exp->get_Expr_Type();
    Type T2 = else_exp->get_Expr_Type();
    if (T1 && T2) {
        return find_type_lca(T1, T2);
    }
    return Null_type;
}


Type loop_class::do_Check_Expr_Type() {
    if (pred->get_Expr_Type() != Bool_type) {
        semant_error(filename, this) << "Condition expression should be Bool" << endl;
    }
    Type T = body->get_Expr_Type();
    return Object_type;
}


Type typcase_class::do_Check_Expr_Type() {
    Type T0 = expr->get_Expr_Type();
    Type T = Null_type;
    if (T0) {
        class_table->enterscope();
        for (int i = cases->first(); cases->more(i); i = cases->next(i)) {
            Case c = cases->nth(i);
            c->install_Case_Type();
            Type Tc = c->check_Case_Type(T0);
            if (!Tc) {
                T = Null_type;
            } else if (T) {
                T = find_type_lca(T, Tc);
            } else {
                T = Tc;
            }
            if (!T) {
                break;
            }
        }
        class_table->exitscope();
    }
    return T;
}


Type block_class::do_Check_Expr_Type() {
    Type T = Object_type;
    for (int i = body->first(); body->more(i) && T; i = body->next(i)) {
        T = body->nth(i)->get_Expr_Type();
    }
    return T;
}


Type let_class::do_Check_Expr_Type() {
    if (identifier == self) {
        semant_error(filename, this) << "Binding self as an identifier" << endl;
    }
    Type T0 = class_table->lookup(type_decl);
    Type T1 = init->is_no_expr() ? T0 : init->get_Expr_Type();
    Type T2 = Null_type;
    if (T0 && T1 && T1.is_sub_type_of(T0)) {
        var_table->enterscope();
        var_table->addid(identifier, T0);
        Type T = body->get_Expr_Type();
        if (T) {
            T2 = T;
        }
        var_table->exitscope();
    }
    if (!T0) {
        semant_error(filename, this) << "Type " << type_decl << " not found" << endl;
    }
    if (T0 && T1 && !T1.is_sub_type_of(T0)) {
        semant_error(filename, this) << "Could not initialize variable " << identifier
            << " of class " << type_decl << " with class " << T1->name << endl;
    }
    return T2;
}


Type plus_class::do_Check_Expr_Type() {
    return arithmetic_type_check(e1, e2, this, "+");
}


Type sub_class::do_Check_Expr_Type() {
    return arithmetic_type_check(e1, e2, this, "-");
}


Type mul_class::do_Check_Expr_Type() {
    return arithmetic_type_check(e1, e2, this, "*");
}


Type divide_class::do_Check_Expr_Type() {
    return arithmetic_type_check(e1, e2, this, "/");
}


Type neg_class::do_Check_Expr_Type() {
    if (e1->get_Expr_Type() != Int_type) {
        semant_error(filename, this) << "operand of ~ should be Int" << endl;
    }
    return Int_type;
}


Type lt_class::do_Check_Expr_Type() {
    arithmetic_type_check(e1, e2, this, "<");
    return Bool_type;
}


Type eq_class::do_Check_Expr_Type() {
    Type T1 = e1->get_Expr_Type();
    Type T2 = e2->get_Expr_Type();
    if (T1 != T2 && (T1 == Int_type || T2 == Int_type || T1 == Bool_type || T2 == Bool_type
        || T1 == String_type || T2 == String_type)){
            semant_error(filename, this) << "Could not compare Int, Bool, or String with other types" << endl;
    }
    return Bool_type;
}


Type leq_class::do_Check_Expr_Type() {
    arithmetic_type_check(e1, e2, this, "<=");
    return Bool_type;
}


Type comp_class::do_Check_Expr_Type() {
    if (e1->get_Expr_Type() != Bool_type) {
        semant_error(filename, this) << "Operator ! can only be applied on Bool expressions" << endl;
    }
    return Bool_type;
}


Type int_const_class::do_Check_Expr_Type() {
    return Int_type;
}


Type bool_const_class::do_Check_Expr_Type() {
    return Bool_type;
}


Type string_const_class::do_Check_Expr_Type() {
    return String_type;
}


Type new__class::do_Check_Expr_Type() {
    Type T = class_table->lookup(type_name);
    if (!T) {
        semant_error(filename, this) << "Class " << type_name << "not defined" << endl;
    }
    return T;
}


Type isvoid_class::do_Check_Expr_Type() {
    Type T1 = e1->get_Expr_Type();
    return Bool_type;
}


Type no_expr_class::do_Check_Expr_Type() {
    return Null_type;
}


Type object_class::do_Check_Expr_Type() {
    Type T = var_table->lookup(name);
    if (!T) {
        semant_error(filename, this) << "Variable " << name << " is not defined" << endl;
    }
    return T;
}

