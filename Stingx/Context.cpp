
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
extern vector<System *> *global_sub_system_list;
void breakfn();

extern int *tt;

#define NO_UNRESOLVED_MULTIPLIER (-1)
#define UNRESOLVED_MULTIPLIER (1)
#define MULTIPLIER_RESOLVED 1
#define ZERO_FORBIDDEN 2
#define ONE_FORBIDDEN 5
#define ZERO_ONE_FORBIDDEN 3
#define ZERO_ONE_ALLOWED 4

void Context::initialize(var_info *f, var_info *fd, var_info *fm)
{
    context_count++;
    this->f = f;
    this->fd = fd;
    this->fm = fm;

    // n= no. of primal dimensions

    n = f->get_dimension();

    // nd=no. of dual dimensions

    nd = fd->get_dimension();

    r = fm->get_dimension();

    factors = new vector<Expression>();
    ms = new MatrixStore(nd, fd);
    ps = new PolyStore(nd, fd);
    ds = new DisequalityStore(r, fm);

    eqs = new vector<Expression>();
    ineqs = new vector<Expression>();
    incon = false;
}

void Context::initialize(var_info *f, var_info *fd, var_info *fm,
                         MatrixStore *ms, PolyStore *ps, DisequalityStore *ds,
                         vector<Expression> *eqs, vector<Expression> *ineqs)
{
    this->f = f;
    this->fd = fd;

    context_count++;
    this->fm = fm;
    n = f->get_dimension();
    nd = fd->get_dimension();
    r = fm->get_dimension();

    this->ms = ms;
    this->ps = ps;
    this->ds = ds;
    this->eqs = eqs;
    this->ineqs = ineqs;

    factors = new vector<Expression>();
    check_consistent();
}

Context::Context(var_info *f, var_info *fd, var_info *fm)
{
    initialize(f, fd, fm);
}

Context::Context(var_info *f, var_info *fd, var_info *fm, MatrixStore *ms,
                 PolyStore *ps, DisequalityStore *ds, vector<Expression> *eqs,
                 vector<Expression> *ineqs)
{
    initialize(f, fd, fm, ms, ps, ds, eqs, ineqs);
}

Context::Context(var_info *f, var_info *fd, var_info *fm, MatrixStore *ms,
                 PolyStore *ps, DisequalityStore *ds)
{
    eqs = new vector<Expression>();
    ineqs = new vector<Expression>();
    initialize(f, fd, fm, ms, ps, ds, eqs, ineqs);
}

void Context::add_equality_expression(Expression l) { eqs->push_back(l); }

void Context::add_inequality_expression(Expression l) { ineqs->push_back(l); }

void Context::add_to_matrix_store(SparseLinExpr l) { ms->add_constraint(l); }

void Context::add_to_matrix_store(Linear_Expression lin)
{
    int i;
    SparseLinExpr l(nd, fd);
    for (i = 0; i < nd; i++) {
        l.set_coefficient(i, handle_integers(lin.coefficient(Variable(i))));
    }

    l.set_coefficient(nd, handle_integers(lin.inhomogeneous_term()));
    ms->add_constraint(l);
}

void Context::add_to_poly_store(SparseLinExpr l)
{
    ps->add_constraint(l, TYPE_GEQ);
}

void Context::add_to_poly_store(Constraint cc)
{
    int i;
    ps->add_constraint(cc);
    if (cc.is_equality()) {
        SparseLinExpr l(nd, fd);
        for (i = 0; i < nd; i++) {
            l.set_coefficient(i, handle_integers(cc.coefficient(Variable(i))));
        }

        l.set_coefficient(nd, handle_integers(cc.inhomogeneous_term()));
        ms->add_constraint(l);
    }

    return;
}

void Context::add_linear_equality(SparseLinExpr l) { add_to_matrix_store(l); }

void Context::add_transform(LinTransform l)
{
    vector<Expression>::iterator vi;
    for (vi = eqs->begin(); vi < eqs->end(); vi++) (*vi).transform(l);

    for (vi = ineqs->begin(); vi < ineqs->end(); vi++) (*vi).transform(l);

    // now add the transform into the disequality store
    ds->add_transform(l);
    return;
}

void Context::add_linear_inequality(SparseLinExpr l) { add_to_poly_store(l); }

void Context::add_transform_inequality(LinTransform l)
{
    // Just add the transform as an expression into the disequality store
    ds->add_transform_inequality(l);
    return;
}

Context *Context::clone() const
{
    // Some references like f,fd,fm, invariant should be passed on
    // ms,ps,ds,eqs,ineqs should be cloned so that they are not rewritten
    MatrixStore *ms1 = ms->clone();
    PolyStore *ps1 = ps->clone();
    DisequalityStore *ds1 = ds->clone();
    vector<Expression> *eqs1 = new vector<Expression>(),
                       *ineqs1 = new vector<Expression>();

    vector<Expression>::iterator vi;

    for (vi = eqs->begin(); vi < eqs->end(); vi++)
        eqs1->push_back(Expression(*vi));

    for (vi = ineqs->begin(); vi < ineqs->end(); vi++)
        ineqs1->push_back(Expression(*vi));

    return new Context(f, fd, fm, ms1, ps1, ds1, eqs1, ineqs1);
}

void Context::check_consistent()
{
    incon =
        !ms->is_consistent() || !ps->is_consistent() || !ds->is_consistent();
}

bool Context::is_consistent()
{
    check_consistent();
    return !incon;
}

/*
bool Context::is_leaf(){

   return false;
}



void Context::update_invariant(){
   ps->add_linear_store(m);

}

*/

void Context::print(ostream &in) const
{
    in << "----------------------------- " << endl;
    in << "- The matrix store:" << endl;
    in << *ms;
    in << endl;

    in << "- The polyhedral store:" << endl;
    in << *ps;
    in << endl;

    in << "- The disequality store:" << endl;
    in << *ds;
    in << endl;

    in << "- The equality expression store:" << endl;
    vector<Expression>::iterator vi;
    for (vi = eqs->begin(); vi < eqs->end(); vi++)
        in << (*vi) << " == 0" << endl;
    in << endl;

    in << "- The inequality expression store:" << endl;
    for (vi = ineqs->begin(); vi < ineqs->end(); vi++)
        in << (*vi) << " >= 0" << endl;

    in << "----------------------------- " << endl;
    return;
}

ostream &operator<<(ostream &in, Context const &c)
{
    c.print(in);
    return in;
}

void Context::remove_trivial_inequalities()
{
    // remove trivial expressions from ineqs
    vector<Expression>::iterator vi;
    vi = ineqs->begin();
    // until we get to a non-trivial beginning expression
    while (vi < ineqs->end() && (*vi).is_zero()) {
        ineqs->erase(ineqs->begin());
        vi = ineqs->begin();
    }

    for (; vi < ineqs->end(); vi++) {
        if ((*vi).is_zero()) {
            ineqs->erase(vi);
            vi--;
        }
    }
}

void Context::remove_trivial_equalities()
{
    // remove the trivial expressions from the vectors eqs
    vector<Expression>::iterator vi;
    vi = eqs->begin();
    // until we get to a non-trivial beginning expression
    while (vi < eqs->end() && (*vi).is_zero()) {
        eqs->erase(eqs->begin());
        vi = eqs->begin();
    }

    for (; vi < eqs->end(); vi++) {
        if ((*vi).is_zero()) {
            eqs->erase(vi);
            vi--;
        }
    }
}

void Context::remove_trivial()
{
    remove_trivial_equalities();
    remove_trivial_inequalities();
}

bool Context::move_constraints_equalities()
{
    // Check eqs for constraints that are linear equalities or linear transforms
    // and In case a linear equality is obtained then transfer it to the
    // equality and inequality stores In case a linear transform is obtained,
    // then apply the transform on all the expressions and
    //   Add it to the disequality store
    // return true if some action occured and false otherwise
    vector<Expression>::iterator vi;
    bool some = false;
    for (vi = eqs->begin(); vi < eqs->end(); vi++) {
        if ((*vi).is_pure_a()) {
            add_linear_equality((*vi).convert_linear());
            some = true;
        }
        else if ((*vi).is_pure_b()) {
            add_transform((*vi).convert_transform());
            some = true;
        }
    }

    return some;
}

bool Context::move_constraints_inequalities()
{
    // check ineqs for constraints that are linear inequalities
    vector<Expression>::iterator vi;
    bool some = false;
    for (vi = ineqs->begin(); vi < ineqs->end(); vi++) {
        if ((*vi).is_pure_a()) {
            add_linear_inequality((*vi).convert_linear());
            ineqs->erase(vi);
            vi--;
            some = true;
            continue;
        }
        else if ((*vi).is_pure_b()) {
            add_transform_inequality((*vi).convert_transform());
            ineqs->erase(vi);
            vi--;
            some = true;
            continue;
        }
    }

    return some;
}

bool Context::move_constraints()
{
    if (move_constraints_equalities() || move_constraints_inequalities()) {
        return true;
    }

    return false;
}

void Context::reconcile_stores()
{
    ps->add_linear_store(*ms);
    ps->extract_linear_part(*ms);

    return;
}

void Context::simplify_equalities()
{
    // simplify each equality and inequality expression against the matrix store
    vector<Expression>::iterator vi;
    for (vi = eqs->begin(); vi < eqs->end(); vi++) {
        (*vi).simplify(*ms);
    }
}

void Context::simplify_inequalities()
{
    vector<Expression>::iterator vi;
    for (vi = ineqs->begin(); vi < ineqs->end(); vi++) {
        (*vi).simplify(*ms);
    }

    // Are there some rules that can be used to simplify the expressions using
    // the polyhedral store?
    // -- TO BE REFINED SUBSEQUENTLY--
}

void Context::simplify()
{
    reconcile_stores();
    simplify_equalities();
    simplify_inequalities();
    remove_trivial();
    return;
}

void Context::simplify_repeat()
{
    bool some = true;
    while (some) {
        some = move_constraints();
        simplify();
        remove_trivial();
    }

    return;
}

bool Context::factor_occurs_equalities(LinTransform &t)
{
    // check if the factor given by LinTransform already occurs
    // if so then increment the "count" of the expression
    vector<Expression>::iterator vi;

    for (vi = factors->begin(); vi < factors->end(); vi++) {
        if ((*vi).get_transform_factor() == t) {
            (*vi).add_count();
            return true;
        }
    }

    return false;
}

bool Context::collect_factors_equalities()
{
    // Run factorize on all the expressions in eqs and then
    // Collect all the expressions that are factored into a single
    // vector factors

    bool some = false;

    vector<Expression>::iterator vi;
    LinTransform temp;

    // First erase factors completely
    factors->erase(factors->begin(), factors->end());

    for (vi = eqs->begin(); vi < eqs->end(); vi++) {
        if ((*vi).factorize()) {
            temp = (*vi).get_transform_factor();
            if (!is_viable_equalities(temp)) {
                (*vi).drop_transform(temp);
            }
            else {
                if (!factor_occurs_equalities(temp)) {
                    (*vi).reset_count();
                    factors->push_back(*vi);
                    some = true;
                }
            }
        }
    }
    return some;
}

Expression &Context::choose_maximal_factor_equalities()
{
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

    vector<Expression>::iterator vi, vj;
    vj = factors->begin();
    vi = factors->begin() + 1;

    while (vi < factors->end()) {
        if ((*vi).get_count() > (*vj).get_count()) {
            vj = vi;
        }
        vi++;
    }
    return (*vj);
}

bool Context::is_viable_equalities(LinTransform &lt)
{
    // check if split on lt==0 is allowed by the disequality constraint store
    return ds->check_status_equalities(lt);
}

bool Context::split_on_factor_equalities(LinTransform &lt)
{
    vector<Expression>::iterator vi;
    bool split = false;
    if (!is_viable_equalities(lt)) {
        // Then each expression that has lt as a factor should drop it
        for (vi = eqs->begin(); vi < eqs->end(); vi++) (*vi).drop_transform(lt);
        simplify_repeat();
    }
    else {
        split = true;
        DisequalityStore *ds1 = ds->clone();
        child1 = new Context(
            f, fd, fm, ms->clone(), ps->clone(),
            ds1);  // create a new context by cloning the appropriate stores
        // cout<<endl<<"- 1. Print Child Context: "<<endl<<(*child1)<<endl;

        // Now add each expression to the appropriate child context
        // child1 will take in lt==0
        // this context  will take in lt <> 0
        for (vi = eqs->begin(); vi < eqs->end(); vi++) {
            if ((*vi).transform_matches(lt)) {
                this->add_to_matrix_store((*vi).get_linear_factor());
                eqs->erase(vi);
                vi--;
            }
            else {
                child1->add_equality_expression(Expression((*vi)));
            }
        }
        // cout<<endl<<"- 2. Print Child Context: "<<endl<<(*child1)<<endl;

        for (vi = ineqs->begin(); vi < ineqs->end(); vi++) {
            child1->add_inequality_expression(Expression((*vi)));
        }
        // cout<<endl<<"- 3. Print Child Context: "<<endl<<(*child1)<<endl;

        child1->add_transform(lt);
        // cout<<endl<<"- 4. Print Child Context: "<<endl<<(*child1)<<endl;

        // KEY: Modify the "Father Context" to be the second child!
        ds->add_transform_negated(lt);

        child1->simplify_repeat();
        // cout<<endl<<"- 5. Print Child Context: "<<endl<<(*child1)<<endl;
        simplify_repeat();
    }

    return split;
}

void Context::print_children(ostream &os)
{
    os << "- First child" << endl;
    os << *child1 << endl;
}

bool Context::is_linear_context()
{
    simplify_repeat();
    if (eqs->empty() && ineqs->empty()) return true;

    return false;
}

int Context::factorizing_strategy_equalities()
{
    // A cover function that calls split, chooses a maximum factor and splits

    if (!collect_factors_equalities())  // No factors found. Nothing to do
        return 0;

    // Now find maximum factor
    bool split = false;
    bool has_factors = true;

    Expression e = choose_maximal_factor_equalities();

    /*
    //Test to print factor
    cout<<endl<<"Expr e is: "<<e<<endl;
    cout<<"Transform factor is: "<<e.get_transform_factor()<<endl;
    */

    split = split_on_factor_equalities(e.get_transform_factor());

    if (split) {
        return 2;
    }
    else {
        while (has_factors && !split) {
            has_factors = collect_factors_equalities();
            e = choose_maximal_factor_equalities();
            split = split_on_factor_equalities(e.get_transform_factor());
        }
    }

    if (split)
        return 2;
    else
        return 0;
}

void Context::recursive_strategy(System &s, C_Polyhedron *dualp)
{
    int i = 1;

    while (i > 0) {
        if (ps->contained(dualp)) {
            prune_count++;
            return;
        }
        i = factorizing_strategy_equalities();

        if (i > 0) {
            child1->recursive_strategy(s, dualp);
            delete (child1);
        }
        else {
            terminal_strategy(s, dualp);
            return;
        }
    }
}

void Context::recursive_strategy(vector<Location *> *loclist,
                                 C_Polyhedron *dualp, int wtime, bool timed)
{
    Timer one_timer;
    recursive_strategy(loclist, dualp, wtime, timed, one_timer);
}

void Context::Convert_CNF_to_DNF_and_Print(vector<Location *> *loclist,
                                           C_Polyhedron *dualp, int wtime,
                                           bool timed)
{
    Timer one_timer;
    Convert_CNF_to_DNF_and_Print(loclist, dualp, wtime, timed, one_timer);
}

void Context::recursive_strategy(vector<Location *> *loclist,
                                 C_Polyhedron *dualp, int wtime, bool timed,
                                 Timer &one_timer)
{
    int i = 1;

    if (timed && one_timer.compute_time_elapsed() >= wtime) {
        cerr << "Time is up" << endl;
        return;
    }

    while (i > 0) {
        if (ps->contained(dualp)) {
            prune_count++;
            return;
        }
        i = factorizing_strategy_equalities();

        if (i > 0) {
            child1->recursive_strategy(loclist, dualp, wtime, timed, one_timer);
            delete (child1);
        }
        else {
            split_01_strategy(loclist, dualp, wtime, timed, one_timer);
            return;
        }
    }
}
void Context::Convert_CNF_to_DNF_and_Print(vector<Location *> *loclist,
                                           C_Polyhedron *dualp, int wtime,
                                           bool timed, Timer &one_timer)
{
    int i = 1;
    if (timed && one_timer.compute_time_elapsed() >= wtime) {
        cerr << "Time is up" << endl;
        return;
    }
    while (i > 0) {
        if (ps->contained(dualp)) {
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
        }
        else {
            split_01_strategy(loclist, dualp, wtime, timed, one_timer);
            return;
        }
    }
}

void Context::recursive_strategy(Clump &vp)
{
    int i = 1;
    while (i > 0) {
        if (vp.contains(ps->get_poly_reference())) {
            prune_count++;
            return;
        }
        i = factorizing_strategy_equalities();
        if (i > 0) {
            // cout<<endl<<"- The Left Child Context: "<<endl; print(cout);
            // cout<<endl<<"- The Right Child Context: "<<endl<<(*child1)<<endl;
            child1->recursive_strategy(vp);
            delete (child1);
        }
        else {
            split_01_strategy(
                vp);  // contains process "vp.insert(ps->get_poly_reference())";
            return;
        }
    }
}

/*
void Context::recursive_strategy(vector<Context *>* children){
   // Can I be split?
   if (ps->is_trivial())
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
void Context::get_multiplier_counts()
{
    int i;

    for (i = 0; i < r; i++) tt[i] = 0;

    vector<Expression>::iterator vi;
    if (eqs->empty() && ineqs->empty()) return;

    for (vi = eqs->begin(); vi < eqs->end(); vi++) {
        (*vi).count_multipliers(tt);
    }

    for (vi = ineqs->begin(); vi < ineqs->end(); vi++) {
        (*vi).count_multipliers(tt);
    }

    return;
}

int Context::get_multiplier_status()
{
    int i;
    // find out about each multiplier
    if ((eqs->empty() && ineqs->empty()) || (!zero && !one)) {
        return NO_UNRESOLVED_MULTIPLIER;
    }

    bool zero_possible, one_possible;
    LinTransform lt(r, fm);

    // now check  on each multiplier on how many unresolved instances are there
    get_multiplier_counts();

    for (i = 0; i < r; i++) {
        if (tt[i] == 0) {
            tt[i] = MULTIPLIER_RESOLVED;
        }
        else {
            lt[i] = 1;
            lt[r] = 0;

            // now test if zero and one are available

            zero_possible = false;
            one_possible = false;

            if (zero) {  // Am I allowed a zero instantiation in the first place

                // check if \mu=0 is viable

                lt[i] = 1;
                if (is_viable_equalities(lt)) zero_possible = true;
            }

            if (one) {  // Am I allowed a one instantiation
                // check if \mu-1 =0 is viable
                lt[r] = -1;
                if (is_viable_equalities(lt)) one_possible = true;
            }

            if (zero_possible) {
                if (one_possible)
                    tt[i] = ZERO_ONE_ALLOWED;
                else
                    tt[i] = ONE_FORBIDDEN;
            }
            else {
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

int Context::choose_unresolved_multiplier()
{
    // make an array and choose the one that is really asking to be
    // split

    int i;

    for (i = 0; i < r; i++) tt[i] = 0;

    vector<Expression>::iterator vi;
    if (eqs->empty() && ineqs->empty()) return NO_UNRESOLVED_MULTIPLIER;

    for (vi = eqs->begin(); vi < eqs->end(); vi++) {
        (*vi).count_multipliers(tt);
    }

    for (vi = ineqs->begin(); vi < ineqs->end(); vi++) {
        (*vi).count_multipliers(tt);
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
   LinTransform lt(r,fm);
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

void Context::terminal_strategy(System &s, C_Polyhedron *dualp)
{
    // compute a new transition relation for each terminal

    int index = get_multiplier_status();

    if (index == NO_UNRESOLVED_MULTIPLIER) {
        // now add the invariants and update dualp
        s.add_invariants_and_update(ps->get_poly_reference(), (*dualp));
        return;  // nothing to be done
    }

    // else print the new system

    System *new_sys = new System(s, (*this));
    global_sub_system_list->push_back(new_sys);

    // print the new system
    cout << " Terminal Transition System :" << endl;
    cout << (*new_sys) << endl;
    cout << endl;

    // that is it
    return;
}

void Context::split_01_strategy(Clump &vp)
{
    // choose an unresolved multiplier and create two children by instantiating
    // with 0 and 1 as long as these instantiations are allowed

    int index = get_multiplier_status();
    int i;
    if (index == NO_UNRESOLVED_MULTIPLIER) {
        // now add the invariants and update dualp
        vp.insert(ps->get_poly_reference());
        return;  // nothing to be done
    }

    // now go though all the multipliers for which zero or one is forbidden and
    // apply the remaining choose 0/1 values for the multiplier and expand
    LinTransform lt(r, fm);
    Context *child1;

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
        vp.insert(ps->get_poly_reference());
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
            child1->recursive_strategy(vp);
            delete (child1);

            lt[i] = 1;
            lt[r] = Rational(-1, 1);
            child1 = this->clone();
            child1->add_transform(lt);
            child1->simplify_repeat();
            child1->recursive_strategy(vp);
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

   PRECONDITION( result.space_dimension()== (unsigned) 2 * nd);

   // first gather all the variables that the index variable relates
   // then gather all the constraints that the index variable has


}

*/

void Context::split_01_strategy(vector<Location *> *loclist,
                                C_Polyhedron *dualp, int wtime, bool timed,
                                Timer &one_timer)
{
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
        (*dualp) = C_Polyhedron(nd, UNIVERSE);
        vector<Location *>::iterator vi;
        for (vi = loclist->begin(); vi < loclist->end(); vi++) {
            (*vi)->extract_invariants_and_update(ps->get_poly_reference(),
                                                 *dualp);
        }
        return;  // nothing to be done
    }

    // now go though all the multipliers for which zero or one is forbidden and
    // apply the remaining choose 0/1 values for the multiplier and expand
    LinTransform lt(r, fm);
    Context *child1;

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
        (*dualp) = C_Polyhedron(nd, UNIVERSE);
        vector<Location *>::iterator vi;
        for (vi = loclist->begin(); vi < loclist->end(); vi++) {
            (*vi)->extract_invariants_and_update(ps->get_poly_reference(),
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

void Context::collect_generators(Generator_System &g)
{
    reconcile_stores();
    if (!is_linear_context()) {
        if (gendrop) validate_generators(g);

        return;
    }
    else {
        // Now just collect the generators into Generator_System from the
        // polynomial store
        ps->collect_generators(g);
    }
}

// Old version, StInG compiling under PPL 0.9 (05/03/2006)
/*
void Context::validate_generators(Generator_System & g){
   Generator_System g1=ps->minimized_generators(); // obtain the minimized
generators from the polystore Generator_System::const_iterator vi;

   for(vi=g1.begin();vi!=g1.end();vi++){
      if (((*vi).is_point()|| (*vi).is_ray()) && is_valid_generator((*vi))){
         g.insert(*vi);
      }
      if ((*vi).is_line()){
         if (is_valid_generator(ray(Linear_Expression(*vi))))
            g.insert(ray(Linear_Expression(*vi)));

         if (is_valid_generator(ray(-Linear_Expression(*vi))))
            g.insert(ray(-Linear_Expression(*vi)));
      }
   }
}
*/

// ***
// New version, StInG compling under PPL 1.2 (05/07/2021),
// updates by Hongming Liu, in Shanghai Jiao Tong University.
// ***
void Context::validate_generators(Generator_System &g)
{
    Generator_System g1 =
        ps->minimized_generators();  // obtain the minimized generators from the
                                     // polystore
    Generator_System::const_iterator vi;

    for (vi = g1.begin(); vi != g1.end(); vi++) {
        if (((*vi).is_point() || (*vi).is_ray()) && is_valid_generator((*vi))) {
            g.insert(*vi);
        }
        if ((*vi).is_line()) {
            // Convert generator (*vi is of line type) to Linear_Expression (no
            // sign for line), then convert Linear_Expression to ray (signed
            // with ray)
            Linear_Expression e;
            for (dimension_type i = (*vi).space_dimension(); i-- > 0;) {
                e += (*vi).coefficient(Variable(i)) * Variable(i);
            }

            if (is_valid_generator(ray(e))) g.insert(ray(e));

            if (is_valid_generator(ray(-e))) g.insert(ray(-e));
        }
    }
}

bool Context::is_valid_generator(Generator const &g)
{
    // check if the generator g is valid by
    // 1. replacing all the eqs and ineqs by transforms
    // 2. Insert them into a clone of the disequality store
    // 3. check the final disequality store for consistency

    DisequalityStore *ds1 = ds->clone();  // clone the disequality store

    vector<Expression>::iterator vi;
    for (vi = eqs->begin(); vi < eqs->end(); vi++) {
        SparseLinExpr p((*vi).to_transform(g));
        ds1->add_constraint(p, TYPE_EQ);
    }

    for (vi = ineqs->begin(); vi < ineqs->end(); vi++) {
        SparseLinExpr p((*vi).to_transform(g));
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
    }
    else {
        delete (ds1);
        return false;
    }
}

Context::~Context()
{
    delete (ms);
    delete (ps);
    delete (ds);
    delete (eqs);
    delete (ineqs);
    delete (factors);
}

void Context::obtain_primal_polyhedron(int left, C_Polyhedron &result)
{
    PRECONDITION((result.space_dimension() == (unsigned)n),
                 " Polyhedron of wrong space dimension passed");

    PRECONDITION((left >= 0 && left + n + 1 <= nd),
                 " Asked to primalize out of range");

    // assume that result's space dimension is =n

    // obtain the generators of the polystore polyhedron
    reconcile_stores();
    C_Polyhedron const &pp = ps->get_nnc_poly_reference();
    Generator_System gs = pp.generators();
    // now make them into constraints
    Generator_System::const_iterator vi;

    Linear_Expression ll;
    int i, j;
    for (vi = gs.begin(); vi != gs.end(); ++vi) {
        ll *= 0;  // reset the linexpr
        for (i = 0; i < n; ++i) {
            j = handle_integers((*vi).coefficient(Variable(left + i)));
            ll += j * Variable(i);
        }

        ll += handle_integers((*vi).coefficient(Variable(left + n)));

        if ((*vi).is_line())
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

bool Context::is_multiplier_present(int index)
{
    PRECONDITION((index >= 0 && index < r),
                 " Context::is_multiplier_present() --- Index out of range");

    vector<Expression>::iterator vi;
    for (vi = eqs->begin(); vi < eqs->end(); ++vi) {
        if ((*vi).is_multiplier_present(index)) return true;
    }
    for (vi = ineqs->begin(); vi < ineqs->end(); ++vi) {
        if ((*vi).is_multiplier_present(index)) return true;
    }
    return false;
}

bool Context::obtain_transition_relation(int mult_index, int left,
                                         C_Polyhedron &result)
{
    //
    // assume that the mutiplier is present .. return "false" otherwise
    //
    //
    // secondly all the constraints involving the multiplier should lie in the
    // range [left.. left+n] or else this will not work
    //

    PRECONDITION((result.space_dimension() == (unsigned)(2 * n)),
                 " result polyhedron not of the correct space dimension");

    PRECONDITION((left >= 0 && left + n + 1 <= nd),
                 " Context::obtain_transtion_relation -- left1 out of range");

    //
    // first create a polyhedron called temp in which constraints on \mu
    // also check if the polyhedron satisfies the constraints above
    //

    C_Polyhedron temp(2 * n + 2, UNIVERSE);
    Linear_Expression ll;

    // vector<Expression>::iterator vi;

    // first handle the equalities

    bool res1 = to_constraints_(mult_index, left, temp, eqs, false);

    if (!res1) {
        // something went wrong
        return false;
    }

    // inequalities

    res1 = to_constraints_(mult_index, left, temp, ineqs, true);

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
        for (i = 0; i < n; i++) {
            j = -handle_integers((*vgs).coefficient(Variable(i)));
            ll += j * Variable(i);
        }

        j = -handle_integers((*vgs).coefficient(Variable(n)));
        ll += j;
        for (i = 0; i < n; i++) {
            j = handle_integers((*vgs).coefficient(Variable(n + 1 + i)));
            ll += j * Variable(n + i);
        }
        j = handle_integers((*vgs).coefficient(Variable(2 * n + 1)));
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

bool Context::to_constraints_(int index, int left, C_Polyhedron &result,
                              vector<Expression> *what, bool ineq)
{
    vector<Expression>::iterator vi;
    Linear_Expression ll;
    int i, j;

    for (vi = what->begin(); vi < what->end(); ++vi) {
        // first check that all the constraints (*vi) has
        // index as its multiplier

        if ((*vi).is_multiplier_present(index) == false) continue;

        (*vi).adjust();

        // it does.. so obtain the LinExpr corresponding to it
        SparseLinExpr mc = (*vi)(index);
        for (i = 0; i < left; ++i)
            if (mc(i) != 0) return false;

        for (i = left + n + 1; i < nd; ++i)
            if (mc(i) != 0) return false;

        // now obtain fill in the constraints for muc
        for (i = 0; i <= n; ++i) {
            j = mc(i + left).num();

            ll += j * Variable(i);
        }

        mc = (*vi)(r);

        for (i = 0; i < left; ++i)
            if (mc(i) != 0) return false;

        for (i = left + n + 1; i < nd; ++i)
            if (mc(i) != 0) return false;

        // now obtain fill in the constraints for c
        for (i = 0; i <= n; ++i) {
            j = mc(i + left).num();

            ll += j * Variable(i + n + 1);
        }
        if (ineq)
            result.add_constraint(ll >= 0);
        else
            result.add_constraint(ll == 0);
    }
    return true;
}
