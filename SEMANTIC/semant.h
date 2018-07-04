#ifndef SEMANT_H_
#define SEMANT_H_

#include <assert.h>
#include <iostream>
#include "cool-tree.h"
#include "stringtab.h"
#include "symtab.h"
#include "list.h"

#define TRUE 1
#define FALSE 0

class ClassTable;
typedef ClassTable *ClassTableP;

struct class_tree_node_type;
typedef class_tree_node_type *class_tree_node;

struct class_method_type;
typedef class_method_type *class_method;

typedef SymbolTable< Symbol, class_tree_node_type> symtable_type;
typedef SymbolTable< Symbol, class_method_type> method_table_type;

extern method_table_type *method_table;

// This is a structure that may be used to contain the semantic
// information such as the inheritance graph.  You may use it or not as
// you like: it is only here to provide a container for the supplied
// methods.

class ClassTable {
private:
  int semant_errors;
  void install_basic_classes();
  ostream& error_stream;

  symtable_type symtable;
  symtable_type vartable;

public:
  ClassTable(Classes);
  int errors() { return semant_errors; }
  ostream& semant_error();
  ostream& semant_error(Class_ c);
  ostream& semant_error(Symbol filename, tree_node *t);
};


struct class_tree_node_type {
    class_tree_node head;
    int rank;
    int size;
    class_tree_node parent;
    class_tree_node child;
    class_tree_node sibiling;
    Class_ contain;
    int depth;
    Symbol name;
    static class_tree_node nodes_head;
    class_tree_node nodes_next;
    method_table_type method_table;

    class_tree_node find_set() {
        return (head == this) ? this : head = head->find_set();
    }


	public:
    friend class_tree_node union_set( class_tree_node, class_tree_node);

    class_tree_node_type(Symbol name, Class_ class_=NULL) : head(this), rank(0), size(1),
        parent(NULL), child(NULL), sibiling(NULL), contain(class_), depth(-1), name(name), nodes_next(nodes_head) {
        nodes_head = this;
        method_table.enterscope();
        if (class_) {
            this->set_contain(contain);
        }
    }

    ~class_tree_node_type() {
        method_table.exitscope();
    }

    bool is_defined() const;

    void set_contain(Class_ c) {
        contain = c;
        ::method_table = &this->method_table;
        return contain->collect_Methods();
    }

    bool set_parent(class_tree_node n) {
        parent = n;
        sibiling = n->child;
        n->child = this;
        return union_set(this, parent);
    }

    bool is_sub_class_of( const class_tree_node_type *super) const
    {
        if ( !is_defined() || !super->is_defined())
        {
            return false;
        }

        const class_tree_node_type *leg = this;
        while ( leg->depth > super->depth)
        {
            leg = leg->parent;
        }

        return leg == super;
    }

    class_method find_method( Symbol name) {
		class_method ret = method_table.lookup( name);
		return ret ? ret : ( parent ? parent->find_method( name) : NULL);
    }

    bool fill_depth();

    static void fill_node_depth() {
        class_tree_node leg = nodes_head;
        while (leg) {
            leg->fill_depth();
            leg = leg->nodes_next;
        }
    }

    bool walk_down();
};

struct class_method_type {
	private:
	Type type;
	class_method next;

	public:
	class_method_type(Type nt, class_method nn=NULL) : type(nt), next(nn) { }

	Type hd() const { return type; }
	class_method tl() const { return next; }

	void set_hd( Type nt) { type = nt; }
	void set_tl( class_method nn) { next = nn; }

	bool is_defined() const { return type; }

	bool is_same_method( class_method t) const;
};


#endif

