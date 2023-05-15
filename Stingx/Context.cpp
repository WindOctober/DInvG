
/*
 * lsting: Invariant Generation using Constraint Solving.
 * Copyright (C) 2005 Sriram Sankaranarayanan < srirams@theory.stanford.edu>
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 *
 */

#include "Context.h"

#include "Clump.h"
#include "Location.h"
#include "System.h"
#include "Timer.h"
#include "myassertions.h"

extern bool gendrop;
extern bool zero;
extern bool one;
extern int prune_count;
extern int context_count;
extern int num_context;
extern vector<System*>* global_sub_system_list;
void breakfn();

extern int* tt;

#define NO_UNRESOLVED_MULTIPLIER (-1)
#define UNRESOLVED_MULTIPLIER (1)
#define MULTIPLIER_RESOLVED 1
#define ZERO_FORBIDDEN 2
#define ONE_FORBIDDEN 5
#define ZERO_ONE_FORBIDDEN 3
#define ZERO_ONE_ALLOWED 4

void Context::initialize(var_info* info, var_info* dual_info, var_info* lambda_info) {
    context_count++;
    this->info = info;
    this->dual_info = dual_info;
    this->lambda_info = lambda_info;

    // vars_num= no. of primal dimensions

    vars_num = info->get_dimension();

    // dual_num=no. of dual dimensions

    dual_num = dual_info->get_dimension();

    r = lambda_info->get_dimension();

    factors = new vector<Expression>();
    equality_mat = new MatrixStore(dual_num, dual_info);
    inequality_store = new PolyStore(dual_num, dual_info);
    lambda_store = new DisequalityStore(r, lambda_info);

    eq_exprs = new vector<Expression>();
    ineq_exprs = new vector<Expression>();
    incon = false;
}

void Context::initialize(var_info* info,
                         var_info* dual_info,
                         var_info* lambda_info,
                         MatrixStore* equality_mat,
                         PolyStore* inequality_store,
                         DisequalityStore* lambda_store,
                         vector<Expression>* eq_exprs,
                         vector<Expression>* ineq_exprs) {
    this->info = info;
    this->dual_info = dual_info;

    context_count++;
    this->lambda_info = lambda_info;
    vars_num = info->get_dimension();
    dual_num = dual_info->get_dimension();
    r = lambda_info->get_dimension();

    this->equality_mat = equality_mat;
    this->inequality_store = inequality_store;
    this->lambda_store = lambda_store;
    this->eq_exprs = eq_exprs;
    this->ineq_exprs = ineq_exprs;

    factors = new vector<Expression>();
    check_consistent();
}

Context::Context(var_info* info, var_info* dual_info, var_info* lambda_info) {
    initialize(info, dual_info, lambda_info);
}

Context::Context(var_info* info,
                 var_info* dual_info,
                 var_info* lambda_info,
                 MatrixStore* equality_mat,
                 PolyStore* inequality_store,
                 DisequalityStore* lambda_store,
                 vector<Expression>* eq_exprs,
                 vector<Expression>* ineq_exprs) {
    initialize(info, dual_info, lambda_info, equality_mat, inequality_store, lambda_store, eq_exprs, ineq_exprs);
}

Context::Context(var_info* info,
                 var_info* dual_info,
                 var_info* lambda_info,
                 MatrixStore* equality_mat,
                 PolyStore* inequality_store,
                 DisequalityStore* lambda_store) {
    eq_exprs = new vector<Expression>();
    ineq_exprs = new vector<Expression>();
    initialize(info, dual_info, lambda_info, equality_mat, inequality_store, lambda_store, eq_exprs, ineq_exprs);
}

void Context::add_equality_expression(Expression l) {
    eq_exprs->push_back(l);
}

void Context::add_inequality_expression(Expression l) {
    ineq_exprs->push_back(l);
}

void Context::add_to_matrix_store(SparseLinExpr l) {
    equality_mat->add_constraint(l);
}

void Context::add_to_matrix_store(Linear_Expression lin) {
    int i;
    SparseLinExpr l(dual_num, dual_info);
    for (i = 0; i < dual_num; i++) {
        l.set_coefficient(i, handle_integers(lin.coefficient(Variable(i))));
    }

    l.set_coefficient(dual_num, handle_integers(lin.inhomogeneous_term()));
    equality_mat->add_constraint(l);
}

void Context::add_to_poly_store(SparseLinExpr l) {
    inequality_store->add_constraint(l, TYPE_GEQ);
}

void Context::add_to_poly_store(Constraint cc) {
    int i;
    inequality_store->add_constraint(cc);
    if (cc.is_equality()) {
        SparseLinExpr l(dual_num, dual_info);
        for (i = 0; i < dual_num; i++) {
            l.set_coefficient(i, handle_integers(cc.coefficient(Variable(i))));
        }

        l.set_coefficient(dual_num, handle_integers(cc.inhomogeneous_term()));
        equality_mat->add_constraint(l);
    }

    return;
}

void Context::add_linear_equality(SparseLinExpr l) {
    add_to_matrix_store(l);
}

void Context::add_transform(LinTransform l) {
    vector<Expression>::iterator it;
    for (it = eq_exprs->begin(); it < eq_exprs->end(); it++)
        (*it).transform(l);

    for (it = ineq_exprs->begin(); it < ineq_exprs->end(); it++)
        (*it).transform(l);

    // now add the transform into the disequality store
    lambda_store->add_transform(l);
    return;
}

void Context::add_linear_inequality(SparseLinExpr l) {
    add_to_poly_store(l);
}

void Context::add_transform_inequality(LinTransform l) {
    // Just add the transform as an expression into the disequality store
    lambda_store->add_transform_inequality(l);
    return;
}

Context* Context::clone() const {
    // Some references like info,dual_info,lambda_info, invariant should be passed on
    // equality_mat,inequality_store,lambda_store,eq_exprs,ineq_exprs should be cloned so that they are not rewritten
    MatrixStore* ms1 = equality_mat->clone();
    PolyStore* ps1 = inequality_store->clone();
    DisequalityStore* ds1 = lambda_store->clone();
    vector<Expression>*eqs1 = new vector<Expression>(),
    *ineqs1 = new vector<Expression>();

    vector<Expression>::iterator it;

    for (it = eq_exprs->begin(); it < eq_exprs->end(); it++)
        eqs1->push_back(Expression(*it));

    for (it = ineq_exprs->begin(); it < ineq_exprs->end(); it++)
        ineqs1->push_back(Expression(*it));

    return new Context(info, dual_info, lambda_info, ms1, ps1, ds1, eqs1, ineqs1);
}

void Context::check_consistent() {
    incon =
        !equality_mat->is_consistent() || !inequality_store->is_consistent() || !lambda_store->is_consistent();
}

bool Context::is_consistent() {
    check_consistent();
    return !incon;
}

/*
bool Context::is_leaf(){

   return false;
}



void Context::update_invariant(){
   inequality_store->add_linear_store(m);

}

*/

void Context::print(ostream& in) const {
    in << "----------------------------- " << endl;
    in << "- The matrix store:" << endl;
    in << *equality_mat;
    in << endl;

    in << "- The polyhedral store:" << endl;
    in << *inequality_store;
    in << endl;

    in << "- The disequality store:" << endl;
    in << *lambda_store;
    in << endl;

    in << "- The equality expression store:" << endl;
    vector<Expression>::iterator it;
    for (it = eq_exprs->begin(); it < eq_exprs->end(); it++)
        in << (*it) << " == 0" << endl;
    in << endl;

    in << "- The inequality expression store:" << endl;
    for (it = ineq_exprs->begin(); it < ineq_exprs->end(); it++)
        in << (*it) << " >= 0" << endl;

    in << "----------------------------- " << endl;
    return;
}

ostream& operator<<(ostream& in, Context const& c) {
    c.print(in);
    return in;
}

void Context::remove_trivial_inequalities() {
    // remove trivial expressions from ineq_exprs
    vector<Expression>::iterator it;
    it = ineq_exprs->begin();
    // until we get to a non-trivial beginning expression
    while (it < ineq_exprs->end() && (*it).is_zero()) {
        ineq_exprs->erase(ineq_exprs->begin());
        it = ineq_exprs->begin();
    }

    for (; it < ineq_exprs->end(); it++) {
        if ((*it).is_zero()) {
            ineq_exprs->erase(it);
            it--;
        }
    }
}

void Context::remove_trivial_equalities() {
    // remove the trivial expressions from the vectors eq_exprs
    vector<Expression>::iterator it;
    it = eq_exprs->begin();
    // until we get to a non-trivial beginning expression
    while (it < eq_exprs->end() && (*it).is_zero()) {
        eq_exprs->erase(eq_exprs->begin());
        it = eq_exprs->begin();
    }

    for (; it < eq_exprs->end(); it++) {
        if ((*it).is_zero()) {
            eq_exprs->erase(it);
            it--;
        }
    }
}

void Context::remove_trivial() {
    remove_trivial_equalities();
    remove_trivial_inequalities();
}

bool Context::move_constraints_equalities() {
    // Check eq_exprs for constraints that are linear equalities or linear transforms
    // and In case a linear equality is obtained then transfer it to the
    // equality and inequality stores In case a linear transform is obtained,
    // then apply the transform on all the expressions and
    //   Add it to the disequality store
    // return true if flag action occured and false otherwise
    vector<Expression>::iterator it;
    bool flag = false;
    for (it = eq_exprs->begin(); it < eq_exprs->end(); it++) {
        if ((*it).is_pure_a()) {
            add_linear_equality((*it).convert_linear());
            flag = true;
        } else if ((*it).is_pure_b()) {
            add_transform((*it).convert_transform());
            flag = true;
        }
    }

    return flag;
}

bool Context::move_constraints_inequalities() {
    // check ineq_exprs for constraints that are linear inequalities
    vector<Expression>::iterator it;
    bool flag = false;
    for (it = ineq_exprs->begin(); it < ineq_exprs->end(); it++) {
        if ((*it).is_pure_a()) {
            add_linear_inequality((*it).convert_linear());
            ineq_exprs->erase(it);
            it--;
            flag = true;
            continue;
        } else if ((*it).is_pure_b()) {
            add_transform_inequality((*it).convert_transform());
            ineq_exprs->erase(it);
            it--;
            flag = true;
            continue;
        }
    }

    return flag;
}

bool Context::move_constraints() {
    if (move_constraints_equalities() || move_constraints_inequalities()) {
        return true;
    }

    return false;
}

void Context::reconcile_stores() {
    inequality_store->add_linear_store(*equality_mat);
    inequality_store->extract_linear_part(*equality_mat);

    return;
}

void Context::simplify_equalities() {
    // simplify each equality and inequality expression against the matrix store
    vector<Expression>::iterator it;
    for (it = eq_exprs->begin(); it < eq_exprs->end(); it++) {
        (*it).simplify(*equality_mat);
    }
}

void Context::simplify_inequalities() {
    vector<Expression>::iterator it;
    for (it = ineq_exprs->begin(); it < ineq_exprs->end(); it++) {
        (*it).simplify(*equality_mat);
    }

    // Are there flag rules that can be used to simplify the expressions using
    // the polyhedral store?
    // -- TO BE REFINED SUBSEQUENTLY--
}

void Context::simplify() {
    reconcile_stores();
    simplify_equalities();
    simplify_inequalities();
    remove_trivial();
    return;
}

void Context::simplify_repeat() {
    bool flag = true;
    while (flag) {
        flag = move_constraints();
        simplify();
        remove_trivial();
    }

    return;
}

bool Context::factor_occurs_equalities(LinTransform& t) {
    // check if the factor given by LinTransform already occurs
    // if so then increment the "count" of the expression
    vector<Expression>::iterator it;

    for (it = factors->begin(); it < factors->end(); it++) {
        if ((*it).get_transform_factor() == t) {
            (*it).add_count();
            return true;
        }
    }

    return false;
}

bool Context::collect_factors_equalities() {
    // Run factorize on all the expressions in eq_exprs and then
    // Collect all the expressions that are factored into a single
    // vector factors

    bool flag = false;

    LinTransform temp;

    factors->clear();

    for (auto it = eq_exprs->begin(); it < eq_exprs->end(); it++) {
        if ((*it).factorize()) {
            temp = (*it).get_transform_factor();
            if (!is_viable_equalities(temp)) {
                (*it).drop_transform(temp);
            } 
            else {
                if (!factor_occurs_equalities(temp)) {
                    (*it).reset_count();
                    factors->push_back(*it);
                    flag = true;
                }
            }
        }
    }
    return flag;
}

Expression& Context::choose_maximal_factor_equalities() {
    // assume that the vector factors is non-empty or else
    // an exception is to be thrown here.

    if (factors->empty()) {
        cerr << " In Context::choose_maximal_factor_equalities()...." << endl
             << endl;
        cerr << "Fatal Error: Asked to choose a maximal factor on an empty "
                "factors "
                "vector"
             << endl;
        cerr << "Exiting in Panic." << endl;
        breakfn();
    }

    vector<Expression>::iterator it, vj;
    vj = factors->begin();
    it = factors->begin() + 1;

    while (it < factors->end()) {
        if ((*it).get_count() > (*vj).get_count()) {
            vj = it;
        }
        it++;
    }
    return (*vj);
}

bool Context::is_viable_equalities(LinTransform& lt) {
    // check if split on lt==0 is allowed by the disequality constraint store
    return lambda_store->check_status_equalities(lt);
}

bool Context::split_on_factor_equalities(LinTransform& lt) {
    vector<Expression>::iterator it;
    bool split = false;
    if (!is_viable_equalities(lt)) {
        // Then each expression that has lt as a factor should drop it
        for (it = eq_exprs->begin(); it < eq_exprs->end(); it++)
            (*it).drop_transform(lt);
        simplify_repeat();
    } else {
        split = true;
        DisequalityStore* ds1 = lambda_store->clone();
        child1 = new Context(
            info, dual_info, lambda_info, equality_mat->clone(), inequality_store->clone(),
            ds1);  // create a new context by cloning the appropriate stores
        // cout<<endl<<"- 1. Print Child Context: "<<endl<<(*child1)<<endl;

        // Now add each expression to the appropriate child context
        // child1 will take in lt==0
        // this context  will take in lt <> 0
        for (it = eq_exprs->begin(); it < eq_exprs->end(); it++) {
            if ((*it).transform_matches(lt)) {
                this->add_to_matrix_store((*it).get_linear_factor());
                eq_exprs->erase(it);
                it--;
            } else {
                child1->add_equality_expression(Expression((*it)));
            }
        }
        // cout<<endl<<"- 2. Print Child Context: "<<endl<<(*child1)<<endl;

        for (it = ineq_exprs->begin(); it < ineq_exprs->end(); it++) {
            child1->add_inequality_expression(Expression((*it)));
        }
        // cout<<endl<<"- 3. Print Child Context: "<<endl<<(*child1)<<endl;

        child1->add_transform(lt);
        // cout<<endl<<"- 4. Print Child Context: "<<endl<<(*child1)<<endl;

        // KEY: Modify the "Father Context" to be the second child!
        lambda_store->add_transform_negated(lt);

        child1->simplify_repeat();
        // cout<<endl<<"- 5. Print Child Context: "<<endl<<(*child1)<<endl;
        simplify_repeat();
    }

    return split;
}

void Context::print_children(ostream& os) {
    os << "- First child" << endl;
    os << *child1 << endl;
}

bool Context::is_linear_context() {
    simplify_repeat();
    if (eq_exprs->empty() && ineq_exprs->empty())
        return true;

    return false;
}

int Context::factorizing_strategy_equalities() {
    // A cover function that calls split, chooses a maximum factor and splits

    if (!collect_factors_equalities())  // No factors found. Nothing to do
        return 0;

    // Now find maximum factor
    bool split = false;
    bool has_factors = true;

    Expression expr = choose_maximal_factor_equalities();

    /*
    //Test to print factor
    cout<<endl<<"Expr e is: "<<e<<endl;
    cout<<"Transform factor is: "<<e.get_transform_factor()<<endl;
    */

    split = split_on_factor_equalities(expr.get_transform_factor());

    if (split) {
        return 2;
    } else {
        while (has_factors && !split) {
            has_factors = collect_factors_equalities();
            expr = choose_maximal_factor_equalities();
            split = split_on_factor_equalities(expr.get_transform_factor());
        }
    }

    if (split)
        return 2;
    else
        return 0;
}

void Context::recursive_strategy(System& s, C_Polyhedron* dualp) {
    int i = 1;

    while (i > 0) {
        if (inequality_store->contained(dualp)) {
            prune_count++;
            return;
        }
        i = factorizing_strategy_equalities();

        if (i > 0) {
            child1->recursive_strategy(s, dualp);
            delete (child1);
        } else {
            terminal_strategy(s, dualp);
            return;
        }
    }
}

void Context::recursive_strategy(vector<Location*>* loclist,
                                 C_Polyhedron* dualp,
                                 int wtime,
                                 bool timed) {
    Timer one_timer;
    recursive_strategy(loclist, dualp, wtime, timed, one_timer);
}

void Context::Convert_CNF_to_DNF_and_Print(vector<Location*>* loclist,
                                           C_Polyhedron* dualp,
                                           int wtime,
                                           bool timed) {
    Timer one_timer;
    Convert_CNF_to_DNF_and_Print(loclist, dualp, wtime, timed, one_timer);
}

void Context::recursive_strategy(vector<Location*>* loclist,
                                 C_Polyhedron* dualp,
                                 int wtime,
                                 bool timed,
                                 Timer& one_timer) {
    int i = 1;

    if (timed && one_timer.compute_time_elapsed() >= wtime) {
        cerr << "Time is up" << endl;
        return;
    }

    while (i > 0) {
        if (inequality_store->contained(dualp)) {
            prune_count++;
            return;
        }
        i = factorizing_strategy_equalities();

        if (i > 0) {
            child1->recursive_strategy(loclist, dualp, wtime, timed, one_timer);
            delete (child1);
        } else {
            split_01_strategy(loclist, dualp, wtime, timed, one_timer);
            return;
        }
    }
}
void Context::Convert_CNF_to_DNF_and_Print(vector<Location*>* loclist,
                                           C_Polyhedron* dualp,
                                           int wtime,
                                           bool timed,
                                           Timer& one_timer) {
    int i = 1;
    if (timed && one_timer.compute_time_elapsed() >= wtime) {
        cerr << "Time is up" << endl;
        return;
    }
    while (i > 0) {
        if (inequality_store->contained(dualp)) {
            prune_count++;
            return;
        }
        i = factorizing_strategy_equalities();
        if (i > 0) {
            // cout<<endl<<"- The Left Child Context: "<<endl;
            // print(cout);
            // cout<<endl<<"- The Right Child Context: "<<endl<<(*child1)<<endl;
            child1->Convert_CNF_to_DNF_and_Print(loclist, dualp, wtime, timed,
                                                 one_timer);
        } else {
            split_01_strategy(loclist, dualp, wtime, timed, one_timer);
            return;
        }
    }
}

void Context::recursive_strategy(Clump& clump) {
    int i = 1;
    while (i > 0) {
        if (clump.contains(inequality_store->get_poly_reference())) {
            prune_count++;
            return;
        }
        i = factorizing_strategy_equalities();
        if (i > 0) {
            // cout<<endl<<"- The Left Child Context: "<<endl; print(cout);
            // cout<<endl<<"- The Right Child Context: "<<endl<<(*child1)<<endl;
            child1->recursive_strategy(clump);
            delete (child1);
        } else {
            split_01_strategy(clump);  // contains process "clump.insert(inequality_store->get_poly_reference())";
            return;
        }
    }
}

/*
void Context::recursive_strategy(vector<Context *>* children){
   // Can I be split?
   if (inequality_store->is_trivial())
      return;

   int i= factorizing_strategy_equalities();
   if (i==0){
      split_01_strategy(children);
   } else{
      child1->recursive_strategy(children);
      child2->recursive_strategy(children);
   }

}
*/
void Context::get_multiplier_counts() {
    int i;

    for (i = 0; i < r; i++)
        tt[i] = 0;

    vector<Expression>::iterator it;
    if (eq_exprs->empty() && ineq_exprs->empty())
        return;

    for (it = eq_exprs->begin(); it < eq_exprs->end(); it++) {
        (*it).count_multipliers(tt);
    }

    for (it = ineq_exprs->begin(); it < ineq_exprs->end(); it++) {
        (*it).count_multipliers(tt);
    }

    return;
}

int Context::get_multiplier_status() {
    int i;
    // find out about each multiplier
    if ((eq_exprs->empty() && ineq_exprs->empty()) || (!zero && !one)) {
        return NO_UNRESOLVED_MULTIPLIER;
    }

    bool zero_possible, one_possible;
    LinTransform lt(r, lambda_info);

    // now check  on each multiplier on how many unresolved instances are there
    get_multiplier_counts();

    for (i = 0; i < r; i++) {
        if (tt[i] == 0) {
            tt[i] = MULTIPLIER_RESOLVED;
        } else {
            lt[i] = 1;
            lt[r] = 0;

            // now test if zero and one are available

            zero_possible = false;
            one_possible = false;

            if (zero) {  // Am I allowed a zero instantiation in the first place

                // check if \mu=0 is viable

                lt[i] = 1;
                if (is_viable_equalities(lt))
                    zero_possible = true;
            }

            if (one) {  // Am I allowed a one instantiation
                // check if \mu-1 =0 is viable
                lt[r] = -1;
                if (is_viable_equalities(lt))
                    one_possible = true;
            }

            if (zero_possible) {
                if (one_possible)
                    tt[i] = ZERO_ONE_ALLOWED;
                else
                    tt[i] = ONE_FORBIDDEN;
            } else {
                if (one_possible)
                    tt[i] = ZERO_FORBIDDEN;
                else
                    tt[i] = ZERO_ONE_FORBIDDEN;
            }
            lt[i] = 0;
            lt[r] = 0;
        }
    }

    return UNRESOLVED_MULTIPLIER;
}

int Context::choose_unresolved_multiplier() {
    // make an array and choose the one that is really asking to be
    // split

    int i;

    for (i = 0; i < r; i++)
        tt[i] = 0;

    vector<Expression>::iterator it;
    if (eq_exprs->empty() && ineq_exprs->empty())
        return NO_UNRESOLVED_MULTIPLIER;

    for (it = eq_exprs->begin(); it < eq_exprs->end(); it++) {
        (*it).count_multipliers(tt);
    }

    for (it = ineq_exprs->begin(); it < ineq_exprs->end(); it++) {
        (*it).count_multipliers(tt);
    }

    int ret = NO_UNRESOLVED_MULTIPLIER, max = 0;

    for (i = 0; i < r; i++) {
        if (tt[i] > max) {
            ret = i;
            max = tt[i];
        }
    }

    return ret;
}
/*
void Context::split_01_strategy(vector <Context *>* children){
   // choose an unresolved multiplier and create two children by instantiating
with 0 and 1
   // as long as these instantiations are allowed
   int index=choose_unresolved_multiplier();
   if (index== NO_UNRESOLVED_MULTIPLIER){
      children->push_back(this);
      return; // nothing to be done
   }


   // choose 0/1 values for the multiplier and expand
   LinTransform lt(r,lambda_info);
   lt[index]=1; // \mu{index}=0

   Context * child1, *child2;

   if (is_viable_equalities(lt)){
      child1=this->clone();
      child1->add_transform(lt);
      child1->simplify_repeat();
      child1->recursive_strategy(children);

   }

   lt[r]=Rational(-1,1);
   if (is_viable_equalities(lt)){
      child2=this->clone();
      child2->add_transform(lt);
      child2->simplify_repeat();
      child2->recursive_strategy(children);
   }





   return;

}


*/

void Context::terminal_strategy(System& s, C_Polyhedron* dualp) {
    // compute a new transition relation for each terminal

    int index = get_multiplier_status();

    if (index == NO_UNRESOLVED_MULTIPLIER) {
        // now add the invariants and update dualp
        s.add_invariants_and_update(inequality_store->get_poly_reference(), (*dualp));
        return;  // nothing to be done
    }

    // else print the new system

    System* new_sys = new System(s, (*this));
    global_sub_system_list->push_back(new_sys);

    // print the new system
    cout << " Terminal Transition System :" << endl;
    cout << (*new_sys) << endl;
    cout << endl;

    // that is it
    return;
}

void Context::split_01_strategy(Clump& clump) {
    // choose an unresolved multiplier and create two children by instantiating
    // with 0 and 1 as long as these instantiations are allowed

    int index = get_multiplier_status();
    int i;
    if (index == NO_UNRESOLVED_MULTIPLIER) {
        // now add the invariants and update dualp
        clump.insert(inequality_store->get_poly_reference());
        return;  // nothing to be done
    }

    // now go though all the multipliers for which zero or one is forbidden and
    // apply the remaining choose 0/1 values for the multiplier and expand
    LinTransform lt(r, lambda_info);
    Context* child1;

    for (i = 0; i < r; i++) {
        switch (tt[i]) {
            case ZERO_ONE_FORBIDDEN:
                continue;
            case ZERO_FORBIDDEN:
                lt[i] = 1;
                lt[r] = -1;
                add_transform(lt);
                lt[i] = 0;
                lt[r] = 0;

                break;

            case ONE_FORBIDDEN:
                lt[i] = 1;
                add_transform(lt);
                lt[i] = 0;
                break;

            default:
                break;
        }
    }
    simplify_repeat();
    index = get_multiplier_status();
    if (index == NO_UNRESOLVED_MULTIPLIER) {
        clump.insert(inequality_store->get_poly_reference());
        return;  // nothing to be done
    }
    // now split on the remaining cases
    for (i = 0; i < r; i++) {
        if (tt[i] == ZERO_ONE_ALLOWED) {
            lt[i] = 1;
            lt[r] = 0;
            child1 = this->clone();
            child1->add_transform(lt);
            child1->simplify_repeat();
            child1->recursive_strategy(clump);
            delete (child1);

            lt[i] = 1;
            lt[r] = Rational(-1, 1);
            child1 = this->clone();
            child1->add_transform(lt);
            child1->simplify_repeat();
            child1->recursive_strategy(clump);
            delete (child1);

            break;
        }
    }

    return;
}

/*
void Context::convert_to_polyhedron(C_Polyhedron & result, index ){

   //
   // later this can be made efficient by just making a polyhedron
   // with just those dimensions that index is involved with
   //

   PRECONDITION( result.space_dimension()== (unsigned) 2 * dual_num);

   // first gather all the variables that the index variable relates
   // then gather all the constraints that the index variable has


}

*/

void Context::split_01_strategy(vector<Location*>* loclist,
                                C_Polyhedron* dualp,
                                int wtime,
                                bool timed,
                                Timer& one_timer) {
    // choose an unresolved multiplier and create two children by instantiating
    // with 0 and 1 as long as these instantiations are allowed

    if (timed && one_timer.compute_time_elapsed() >= wtime) {
        cerr << "Time is up" << endl;
        return;
    }

    int index = get_multiplier_status();
    int i;
    if (index == NO_UNRESOLVED_MULTIPLIER) {
        // now add the invariants and update dualp
        (*dualp) = C_Polyhedron(dual_num, UNIVERSE);
        vector<Location*>::iterator it;
        for (it = loclist->begin(); it < loclist->end(); it++) {
            (*it)->extract_invariants_and_update(inequality_store->get_poly_reference(),
                                                 *dualp);
        }
        return;  // nothing to be done
    }

    // now go though all the multipliers for which zero or one is forbidden and
    // apply the remaining choose 0/1 values for the multiplier and expand
    LinTransform lt(r, lambda_info);
    Context* child1;

    for (i = 0; i < r; i++) {
        switch (tt[i]) {
            case ZERO_ONE_FORBIDDEN:
                continue;
            case ZERO_FORBIDDEN:
                lt[i] = 1;
                lt[r] = -1;
                add_transform(lt);
                lt[i] = 0;
                lt[r] = 0;

                break;

            case ONE_FORBIDDEN:
                lt[i] = 1;
                add_transform(lt);
                lt[i] = 0;
                break;

            default:
                break;
        }
    }
    simplify_repeat();
    index = get_multiplier_status();
    if (index == NO_UNRESOLVED_MULTIPLIER) {
        // now add the invariants and update dualp
        (*dualp) = C_Polyhedron(dual_num, UNIVERSE);
        vector<Location*>::iterator it;
        for (it = loclist->begin(); it < loclist->end(); it++) {
            (*it)->extract_invariants_and_update(inequality_store->get_poly_reference(),
                                                 *dualp);
        }
        return;  // nothing to be done
    }
    // now split on the remaining cases
    for (i = 0; i < r; i++) {
        if (tt[i] == ZERO_ONE_ALLOWED) {
            lt[i] = 1;
            child1 = this->clone();
            child1->add_transform(lt);
            child1->simplify_repeat();
            child1->recursive_strategy(loclist, dualp, wtime, timed, one_timer);
            delete (child1);

            lt[i] = 1;
            lt[r] = Rational(-1, 1);

            child1 = this->clone();
            child1->add_transform(lt);
            child1->simplify_repeat();
            child1->recursive_strategy(loclist, dualp, wtime, timed, one_timer);
            delete (child1);

            break;
        }
    }

    return;
}

void Context::collect_generators(Generator_System& g) {
    reconcile_stores();
    if (!is_linear_context()) {
        if (gendrop)
            validate_generators(g);

        return;
    } else {
        // Now just collect the generators into Generator_System from the
        // polynomial store
        inequality_store->collect_generators(g);
    }
}

// Old version, StInG compiling under PPL 0.9 (05/03/2006)
/*
void Context::validate_generators(Generator_System & g){
   Generator_System g1=inequality_store->minimized_generators(); // obtain the minimized
generators from the polystore Generator_System::const_iterator it;

   for(it=g1.begin();it!=g1.end();it++){
      if (((*it).is_point()|| (*it).is_ray()) && is_valid_generator((*it))){
         g.insert(*it);
      }
      if ((*it).is_line()){
         if (is_valid_generator(ray(Linear_Expression(*it))))
            g.insert(ray(Linear_Expression(*it)));

         if (is_valid_generator(ray(-Linear_Expression(*it))))
            g.insert(ray(-Linear_Expression(*it)));
      }
   }
}
*/

// ***
// New version, StInG compling under PPL 1.2 (05/07/2021),
// updates by Hongming Liu, in Shanghai Jiao Tong University.
// ***
void Context::validate_generators(Generator_System& g) {
    Generator_System g1 =
        inequality_store->minimized_generators();  // obtain the minimized generators from the
                                     // polystore
    Generator_System::const_iterator it;

    for (it = g1.begin(); it != g1.end(); it++) {
        if (((*it).is_point() || (*it).is_ray()) && is_valid_generator((*it))) {
            g.insert(*it);
        }
        if ((*it).is_line()) {
            // Convert generator (*it is of line type) to Linear_Expression (no
            // sign for line), then convert Linear_Expression to ray (signed
            // with ray)
            Linear_Expression e;
            for (dimension_type i = (*it).space_dimension(); i-- > 0;) {
                e += (*it).coefficient(Variable(i)) * Variable(i);
            }

            if (is_valid_generator(ray(e)))
                g.insert(ray(e));

            if (is_valid_generator(ray(-e)))
                g.insert(ray(-e));
        }
    }
}

bool Context::is_valid_generator(Generator const& g) {
    // check if the generator g is valid by
    // 1. replacing all the eq_exprs and ineq_exprs by transforms
    // 2. Insert them into a clone of the disequality store
    // 3. check the final disequality store for consistency

    DisequalityStore* ds1 = lambda_store->clone();  // clone the disequality store

    vector<Expression>::iterator it;
    for (it = eq_exprs->begin(); it < eq_exprs->end(); it++) {
        SparseLinExpr p((*it).to_transform(g));
        ds1->add_constraint(p, TYPE_EQ);
    }

    for (it = ineq_exprs->begin(); it < ineq_exprs->end(); it++) {
        SparseLinExpr p((*it).to_transform(g));
        ds1->add_constraint(p, TYPE_GEQ);
    }

#ifdef __DEBUG__D_

    cout << "Testing generator::" << g << endl;
    cout << (*ds1) << endl;
    cout << "----------------------------------" << endl;
#endif

    if (ds1->is_consistent()) {
        // This could be a problem
        delete (ds1);
        return true;
    } else {
        delete (ds1);
        return false;
    }
}

Context::~Context() {
    delete (equality_mat);
    delete (inequality_store);
    delete (lambda_store);
    delete (eq_exprs);
    delete (ineq_exprs);
    delete (factors);
}

void Context::obtain_primal_polyhedron(int left, C_Polyhedron& result) {
    PRECONDITION((result.space_dimension() == (unsigned)vars_num),
                 " Polyhedron of wrong space dimension passed");

    PRECONDITION((left >= 0 && left + vars_num + 1 <= dual_num),
                 " Asked to primalize out of range");

    // assume that result's space dimension is =vars_num

    // obtain the generators of the polystore polyhedron
    reconcile_stores();
    C_Polyhedron const& pp = inequality_store->get_nnc_poly_reference();
    Generator_System gs = pp.generators();
    // now make them into constraints
    Generator_System::const_iterator it;

    Linear_Expression ll;
    int i, j;
    for (it = gs.begin(); it != gs.end(); ++it) {
        ll *= 0;  // reset the linexpr
        for (i = 0; i < vars_num; ++i) {
            j = handle_integers((*it).coefficient(Variable(left + i)));
            ll += j * Variable(i);
        }

        ll += handle_integers((*it).coefficient(Variable(left + vars_num)));

        if ((*it).is_line())
            // ppl-v0.9
            // result.add_constraint_and_minimize(ll==0);
            // ppl-v1.2 (not certainly)
            result.add_constraint(ll == 0);
        else
            // ppl-v0.9
            // result.add_constraint_and_minimize(ll>=0);
            //  ppl-v1.2 (not certainly)
            result.add_constraint(ll >= 0);
    }

    return;
}

bool Context::is_multiplier_present(int index) {
    PRECONDITION((index >= 0 && index < r),
                 " Context::is_multiplier_present() --- Index out of range");

    vector<Expression>::iterator it;
    for (it = eq_exprs->begin(); it < eq_exprs->end(); ++it) {
        if ((*it).is_multiplier_present(index))
            return true;
    }
    for (it = ineq_exprs->begin(); it < ineq_exprs->end(); ++it) {
        if ((*it).is_multiplier_present(index))
            return true;
    }
    return false;
}

bool Context::obtain_transition_relation(int mult_index,
                                         int left,
                                         C_Polyhedron& result) {
    //
    // assume that the mutiplier is present .. return "false" otherwise
    //
    //
    // secondly all the constraints involving the multiplier should lie in the
    // range [left.. left+vars_num] or else this will not work
    //

    PRECONDITION((result.space_dimension() == (unsigned)(2 * vars_num)),
                 " result polyhedron not of the correct space dimension");

    PRECONDITION((left >= 0 && left + vars_num + 1 <= dual_num),
                 " Context::obtain_transtion_relation -- left1 out of range");

    //
    // first create a polyhedron called temp in which constraints on \mu
    // also check if the polyhedron satisfies the constraints above
    //

    C_Polyhedron temp(2 * vars_num + 2, UNIVERSE);
    Linear_Expression ll;

    // vector<Expression>::iterator it;

    // first handle the equalities

    bool res1 = to_constraints_(mult_index, left, temp, eq_exprs, false);

    if (!res1) {
        // something went wrong
        return false;
    }

    // inequalities

    res1 = to_constraints_(mult_index, left, temp, ineq_exprs, true);

    if (!res1) {
        return false;
    }

    // now obtain the generators of tmp..
    // each generator is of the form mc1 , ... ,mcn, md, c1... , cn, d

    // this should translate to the transition relation
    //         -mc1 x1 - mc2 x2 ... -mcn xn - md + c1 x1' + ... + cn xn' +d <><>
    //         0

    int i, j;

    Generator_System gs = temp.minimized_generators();
    Generator_System::const_iterator vgs;

    for (vgs = gs.begin(); vgs != gs.end(); ++vgs) {
        ll *= 0;
        for (i = 0; i < vars_num; i++) {
            j = -handle_integers((*vgs).coefficient(Variable(i)));
            ll += j * Variable(i);
        }

        j = -handle_integers((*vgs).coefficient(Variable(vars_num)));
        ll += j;
        for (i = 0; i < vars_num; i++) {
            j = handle_integers((*vgs).coefficient(Variable(vars_num + 1 + i)));
            ll += j * Variable(vars_num + i);
        }
        j = handle_integers((*vgs).coefficient(Variable(2 * vars_num + 1)));
        ll += j;

        if ((*vgs).is_line())
            // ppl-v0.9
            // result.add_constraint_and_minimize(ll==0);
            // ppl-v1.2 (not certainly)
            result.add_constraint(ll == 0);
        else
            // ppl-v0.9
            // result.add_constraint_and_minimize(ll>=0);
            // ppl-v1.2 (not certainly)
            result.add_constraint(ll >= 0);
    }

    return true;
}

bool Context::to_constraints_(int index,
                              int left,
                              C_Polyhedron& result,
                              vector<Expression>* what,
                              bool ineq) {
    vector<Expression>::iterator it;
    Linear_Expression ll;
    int i, j;

    for (it = what->begin(); it < what->end(); ++it) {
        // first check that all the constraints (*it) has
        // index as its multiplier

        if ((*it).is_multiplier_present(index) == false)
            continue;

        (*it).adjust();

        // it does.. so obtain the LinExpr corresponding to it
        SparseLinExpr mc = (*it)(index);
        for (i = 0; i < left; ++i)
            if (mc(i) != 0)
                return false;

        for (i = left + vars_num + 1; i < dual_num; ++i)
            if (mc(i) != 0)
                return false;

        // now obtain fill in the constraints for muc
        for (i = 0; i <= vars_num; ++i) {
            j = mc(i + left).num();

            ll += j * Variable(i);
        }

        mc = (*it)(r);

        for (i = 0; i < left; ++i)
            if (mc(i) != 0)
                return false;

        for (i = left + vars_num + 1; i < dual_num; ++i)
            if (mc(i) != 0)
                return false;

        // now obtain fill in the constraints for c
        for (i = 0; i <= vars_num; ++i) {
            j = mc(i + left).num();

            ll += j * Variable(i + vars_num + 1);
        }
        if (ineq)
            result.add_constraint(ll >= 0);
        else
            result.add_constraint(ll == 0);
    }
    return true;
}
