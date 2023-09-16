
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

void Context::initialize(var_info* info,
                         var_info* coefInfo,
                         var_info* lambdaInfo) {
    context_count++;
    this->info = info;
    this->coefInfo = coefInfo;
    this->lambdaInfo = lambdaInfo;

    varsNum = info->getDim();
    coefNum = coefInfo->getDim();
    lambdaNum = lambdaInfo->getDim();

    factors = new vector<Expression>();
    equalStore = new MatrixStore(coefNum, coefInfo);
    polyStore = new PolyStore(coefNum, coefInfo);
    disequalStore = new DisequalityStore(lambdaNum, lambdaInfo);

    eqExprs = new vector<Expression>();
    ineqExprs = new vector<Expression>();
    ConsistencyFlag = false;
}

void Context::initialize(var_info* info,
                         var_info* coefInfo,
                         var_info* lambdaInfo,
                         MatrixStore* equalStore,
                         PolyStore* polyStore,
                         DisequalityStore* disequalStore,
                         vector<Expression>* eqExprs,
                         vector<Expression>* ineqExprs) {
    this->info = info;
    this->coefInfo = coefInfo;

    context_count++;
    this->lambdaInfo = lambdaInfo;
    varsNum = info->getDim();
    coefNum = coefInfo->getDim();
    lambdaNum = lambdaInfo->getDim();

    this->equalStore = equalStore;
    this->polyStore = polyStore;
    this->disequalStore = disequalStore;
    this->eqExprs = eqExprs;
    this->ineqExprs = ineqExprs;

    factors = new vector<Expression>();
    checkConsistent();
}

Context::Context(var_info* info, var_info* coefInfo, var_info* lambdaInfo) {
    initialize(info, coefInfo, lambdaInfo);
}

Context::Context(var_info* info,
                 var_info* coefInfo,
                 var_info* lambdaInfo,
                 MatrixStore* equalStore,
                 PolyStore* polyStore,
                 DisequalityStore* disequalStore,
                 vector<Expression>* eqExprs,
                 vector<Expression>* ineqExprs) {
    initialize(info, coefInfo, lambdaInfo, equalStore, polyStore, disequalStore,
               eqExprs, ineqExprs);
}

Context::Context(var_info* info,
                 var_info* coefInfo,
                 var_info* lambdaInfo,
                 MatrixStore* equalStore,
                 PolyStore* polyStore,
                 DisequalityStore* disequalStore) {
    eqExprs = new vector<Expression>();
    ineqExprs = new vector<Expression>();
    initialize(info, coefInfo, lambdaInfo, equalStore, polyStore, disequalStore,
               eqExprs, ineqExprs);
}

void Context::addEqExpr(Expression l) {
    eqExprs->push_back(l);
}

void Context::addIneqExpr(Expression l) {
    ineqExprs->push_back(l);
}

void Context::insertMatStore(SparseLinExpr l) {
    equalStore->add_constraint(l);
}

void Context::insertMatStore(Linear_Expression lin) {
    int i;
    SparseLinExpr l(coefNum, coefInfo);
    for (i = 0; i < coefNum; i++) {
        l.set_coefficient(i, handle_integers(lin.coefficient(Variable(i))));
    }

    l.set_coefficient(coefNum, handle_integers(lin.inhomogeneous_term()));
    equalStore->add_constraint(l);
}

void Context::insertPolyStore(SparseLinExpr l) {
    polyStore->add_constraint(l, TYPE_GEQ);
}

void Context::insertPolyStore(Constraint constraint) {
    int i;
    polyStore->add_constraint(constraint);  // the constarint on coef of template
                                    // derived from initial condition.
    if (constraint.is_equality()) {
        SparseLinExpr l(coefNum, coefInfo);
        for (i = 0; i < coefNum; i++) {
            l.set_coefficient(i, handle_integers(constraint.coefficient(Variable(i))));
        }
        l.set_coefficient(coefNum, handle_integers(constraint.inhomogeneous_term()));
        equalStore->add_constraint(l);  // the constraint of equality.
    }

    return;
}

void Context::add_linear_equality(SparseLinExpr l) {
    insertMatStore(l);
}

void Context::addTransform(LinTransform l) {
    vector<Expression>::iterator it;
    for (it = eqExprs->begin(); it < eqExprs->end(); it++)
        (*it).transform(l);

    for (it = ineqExprs->begin(); it < ineqExprs->end(); it++)
        (*it).transform(l);

    // now add the transform into the disequality store
    disequalStore->addTransform(l);
    return;
}

void Context::add_linear_inequality(SparseLinExpr l) {
    insertPolyStore(l);
}

void Context::add_transform_inequality(LinTransform l) {
    // Just add the transform as an expression into the disequality store
    disequalStore->add_transform_inequality(l);
    return;
}

Context* Context::clone() const {
    // Some references like info,coefInfo,lambdaInfo, invariant should be passed
    // on equalStore,polyStore,disequalStore,eqExprs,ineqExprs should be cloned so
    // that they are not rewritten
    MatrixStore* ms1 = equalStore->clone();
    PolyStore* ps1 = polyStore->clone();
    DisequalityStore* ds1 = disequalStore->clone();
    vector<Expression>*eqs1 = new vector<Expression>(),
    *ineqs1 = new vector<Expression>();

    vector<Expression>::iterator it;

    for (it = eqExprs->begin(); it < eqExprs->end(); it++)
        eqs1->push_back(Expression(*it));

    for (it = ineqExprs->begin(); it < ineqExprs->end(); it++)
        ineqs1->push_back(Expression(*it));

    return new Context(info, coefInfo, lambdaInfo, ms1, ps1, ds1, eqs1, ineqs1);
}

void Context::checkConsistent() {
    ConsistencyFlag = !equalStore->is_consistent() || !polyStore->is_consistent() ||
            !disequalStore->is_consistent();
}

bool Context::is_consistent() {
    checkConsistent();
    return !ConsistencyFlag;
}

/*
bool Context::is_leaf(){

   return false;
}



void Context::update_invariant(){
   polyStore->add_linear_store(m);

}

*/

void Context::print(ostream& in) const {
    in << "----------------------------- " << endl;
    in << "- The matrix store:" << endl;
    in << *equalStore;
    in << endl;

    in << "- The polyhedral store:" << endl;
    in << *polyStore;
    in << endl;

    in << "- The disequality store:" << endl;
    in << *disequalStore;
    in << endl;

    in << "- The equality expression store:" << endl;
    vector<Expression>::iterator it;
    for (it = eqExprs->begin(); it < eqExprs->end(); it++)
        in << (*it) << " == 0" << endl;
    in << endl;

    in << "- The inequality expression store:" << endl;
    for (it = ineqExprs->begin(); it < ineqExprs->end(); it++)
        in << (*it) << " >= 0" << endl;

    in << "----------------------------- " << endl;
    return;
}

ostream& operator<<(ostream& in, Context const& c) {
    c.print(in);
    return in;
}

void Context::remove_trivial_inequalities() {
    // remove trivial expressions from ineqExprs
    vector<Expression>::iterator it;
    it = ineqExprs->begin();
    // until we get to a non-trivial beginning expression
    while (it < ineqExprs->end() && (*it).isZero()) {
        ineqExprs->erase(ineqExprs->begin());
        it = ineqExprs->begin();
    }

    for (; it < ineqExprs->end(); it++) {
        if ((*it).isZero()) {
            ineqExprs->erase(it);
            it--;
        }
    }
}

void Context::remove_trivial_equalities() {
    // remove the trivial expressions from the vectors eqExprs
    vector<Expression>::iterator it;
    it = eqExprs->begin();
    // until we get to a non-trivial beginning expression
    while (it < eqExprs->end() && (*it).isZero()) {
        eqExprs->erase(eqExprs->begin());
        it = eqExprs->begin();
    }

    for (; it < eqExprs->end(); it++) {
        if ((*it).isZero()) {
            eqExprs->erase(it);
            it--;
        }
    }
}

void Context::remove_trivial() {
    remove_trivial_equalities();
    remove_trivial_inequalities();
}

bool Context::move_constraints_equalities() {
    // Check eqExprs for constraints that are linear equalities or linear
    // transforms and In case a linear equality is obtained then transfer it to
    // the equality and inequality stores In case a linear transform is
    // obtained, then apply the transform on all the expressions and
    //   Add it to the disequality store
    // return true if flag action occured and false otherwise
    vector<Expression>::iterator it;
    bool flag = false;
    for (it = eqExprs->begin(); it < eqExprs->end(); it++) {
        if ((*it).is_pure_a()) {
            add_linear_equality((*it).convert_linear());
            flag = true;
        } else if ((*it).is_pure_b()) {
            addTransform((*it).convert_transform());
            flag = true;
        }
    }

    return flag;
}

bool Context::move_constraints_inequalities() {
    // check ineqExprs for constraints that are linear inequalities
    vector<Expression>::iterator it;
    bool flag = false;
    for (it = ineqExprs->begin(); it < ineqExprs->end(); it++) {
        if ((*it).is_pure_a()) {
            add_linear_inequality((*it).convert_linear());
            ineqExprs->erase(it);
            it--;
            flag = true;
            continue;
        } else if ((*it).is_pure_b()) {
            add_transform_inequality((*it).convert_transform());
            ineqExprs->erase(it);
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
    polyStore->add_linear_store(*equalStore);
    polyStore->extract_linear_part(*equalStore);

    return;
}

void Context::simplify_equalities() {
    // simplify each equality and inequality expression against the matrix store
    vector<Expression>::iterator it;
    for (it = eqExprs->begin(); it < eqExprs->end(); it++) {
        (*it).simplify(*equalStore);
    }
}

void Context::simplify_inequalities() {
    vector<Expression>::iterator it;
    for (it = ineqExprs->begin(); it < ineqExprs->end(); it++) {
        (*it).simplify(*equalStore);
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
        if ((*it).getTransformFactor() == t) {
            (*it).add_count();
            return true;
        }
    }

    return false;
}

bool Context::collect_factors_equalities() {
    // Run factorize on all the expressions in eqExprs and then
    // Collect all the expressions that are factored into a single
    // vector factors

    bool flag = false;
    LinTransform temp;
    factors->clear();
    for (auto it = eqExprs->begin(); it < eqExprs->end(); it++) {
        if ((*it).factorize()) {
            temp = (*it).getTransformFactor();
            if (!isVisableEquals(temp)) {
                (*it).drop_transform(temp);
            } else {
                if (!factor_occurs_equalities(temp)) {
                    (*it).resetCounter();
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
    }

    vector<Expression>::iterator it, vj;
    vj = factors->begin();
    it = factors->begin() + 1;

    while (it < factors->end()) {
        if ((*it).getCount() > (*vj).getCount()) {
            vj = it;
        }
        it++;
    }
    return (*vj);
}

bool Context::isVisableEquals(LinTransform& lt) {
    // check if split on lt==0 is allowed by the disequality constraint store
    return disequalStore->check_status_equalities(lt);
}

bool Context::splitFactorEquals(LinTransform& lt) {
    vector<Expression>::iterator it;
    bool split = false;
    if (!isVisableEquals(lt)) {
        // Then each expression that has lt as a factor should drop it
        for (it = eqExprs->begin(); it < eqExprs->end(); it++)
            (*it).drop_transform(lt);
        simplify_repeat();
    } else {
        split = true;
        childClump = new Context(
            info, coefInfo, lambdaInfo, equalStore->clone(), polyStore->clone(),
            disequalStore->clone());  // create a new context by cloning the
                                     // appropriate stores

        // Now add each expression to the appropriate child context
        // childClump will take in lt==0
        // this context  will take in lt <> 0
        for (it = eqExprs->begin(); it < eqExprs->end(); it++) {
            if ((*it).transform_matches(lt)) {
                this->insertMatStore((*it).getLinFactor());
                eqExprs->erase(it);
                it--;
            } else {
                childClump->addEqExpr(Expression((*it)));
            }
        }
        for (it = ineqExprs->begin(); it < ineqExprs->end(); it++) {
            childClump->addIneqExpr(Expression((*it)));
        }
        childClump->addTransform(lt);
        // KEY: Modify the "Father Context" to be the second child!
        disequalStore->add_transform_negated(lt);
        childClump->simplify_repeat();
        simplify_repeat();
    }

    return split;
}

void Context::print_children(ostream& os) {
    os << "- First child" << endl;
    os << *childClump << endl;
}

bool Context::is_linear_context() {
    simplify_repeat();
    if (eqExprs->empty() && ineqExprs->empty())
        return true;

    return false;
}

bool Context::factorizationSplit() {
    // A cover function that calls split, chooses a maximum factor and splits
    bool split = false;
    bool factorFlag;
    while (!split) {
        factorFlag = collect_factors_equalities();
        if (!factorFlag) return false;
        Expression expr = choose_maximal_factor_equalities();
        split = splitFactorEquals(expr.getTransformFactor());
    }

    return true;
}

void Context::RecursiveSplit(System& s, C_Polyhedron* dualp) {
    int i = 1;

    while (i > 0) {
        if (polyStore->contained(dualp)) {
            prune_count++;
            return;
        }
        i = factorizationSplit();

        if (i > 0) {
            childClump->RecursiveSplit(s, dualp);
            delete (childClump);
        } else {
            terminal_strategy(s, dualp);
            return;
        }
    }
}

void Context::RecursiveSplit(vector<Location*>* loclist,
                                 C_Polyhedron* dualp,
                                 int wtime,
                                 bool timed) {
    Timer one_timer;
    RecursiveSplit(loclist, dualp, wtime, timed, one_timer);
}

void Context::Convert_CNF_to_DNF_and_Print(vector<Location*>* loclist,
                                           C_Polyhedron* dualp,
                                           int wtime,
                                           bool timed) {
    Timer one_timer;
    Convert_CNF_to_DNF_and_Print(loclist, dualp, wtime, timed, one_timer);
}

void Context::RecursiveSplit(vector<Location*>* loclist,
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
        if (polyStore->contained(dualp)) {
            prune_count++;
            return;
        }
        i = factorizationSplit();

        if (i > 0) {
            childClump->RecursiveSplit(loclist, dualp, wtime, timed, one_timer);
            delete (childClump);
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
        if (polyStore->contained(dualp)) {
            prune_count++;
            return;
        }
        i = factorizationSplit();
        if (i > 0) {
            // cout<<endl<<"- The Left Child Context: "<<endl;
            // print(cout);
            // cout<<endl<<"- The Right Child Context: "<<endl<<(*childClump)<<endl;
            childClump->Convert_CNF_to_DNF_and_Print(loclist, dualp, wtime, timed,
                                                 one_timer);
        } else {
            split_01_strategy(loclist, dualp, wtime, timed, one_timer);
            return;
        }
    }
}

void Context::RecursiveSplit(Clump& clump) {
    bool flag = true;
    while (flag) {
        if (clump.contains(polyStore->getPolyRef())) {
            prune_count++;
            return;
        }
        flag = factorizationSplit();
        if (flag) {
            childClump->RecursiveSplit(clump);
            delete (childClump);
        } else {
            split_01_strategy(clump);  // contains process
            return;
        }
    }
}

void Context::get_multiplier_counts() {
    int i;

    for (i = 0; i < lambdaNum; i++)
        tt[i] = 0;

    vector<Expression>::iterator it;
    if (eqExprs->empty() && ineqExprs->empty())
        return;

    for (it = eqExprs->begin(); it < eqExprs->end(); it++) {
        (*it).count_multipliers(tt);
    }

    for (it = ineqExprs->begin(); it < ineqExprs->end(); it++) {
        (*it).count_multipliers(tt);
    }

    return;
}

int Context::get_multiplier_status() {
    int i;
    // find out about each multiplier
    if ((eqExprs->empty() && ineqExprs->empty()) || (!zero && !one)) {
        return NO_UNRESOLVED_MULTIPLIER;
    }

    bool zero_possible, one_possible;
    LinTransform lt(lambdaNum, lambdaInfo);

    // now check  on each multiplier on how many unresolved instances are there
    get_multiplier_counts();

    for (i = 0; i < lambdaNum; i++) {
        if (tt[i] == 0) {
            tt[i] = MULTIPLIER_RESOLVED;
        } else {
            lt[i] = 1;
            lt[lambdaNum] = 0;

            // now test if zero and one are available

            zero_possible = false;
            one_possible = false;

            if (zero) {  // Am I allowed a zero instantiation in the first place

                // check if \mu=0 is viable

                lt[i] = 1;
                if (isVisableEquals(lt))
                    zero_possible = true;
            }

            if (one) {  // Am I allowed a one instantiation
                // check if \mu-1 =0 is viable
                lt[lambdaNum] = -1;
                if (isVisableEquals(lt))
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
            lt[lambdaNum] = 0;
        }
    }

    return UNRESOLVED_MULTIPLIER;
}

int Context::choose_unresolved_multiplier() {
    // make an array and choose the one that is really asking to be
    // split

    int i;

    for (i = 0; i < lambdaNum; i++)
        tt[i] = 0;

    vector<Expression>::iterator it;
    if (eqExprs->empty() && ineqExprs->empty())
        return NO_UNRESOLVED_MULTIPLIER;

    for (it = eqExprs->begin(); it < eqExprs->end(); it++) {
        (*it).count_multipliers(tt);
    }

    for (it = ineqExprs->begin(); it < ineqExprs->end(); it++) {
        (*it).count_multipliers(tt);
    }

    int ret = NO_UNRESOLVED_MULTIPLIER, max = 0;

    for (i = 0; i < lambdaNum; i++) {
        if (tt[i] > max) {
            ret = i;
            max = tt[i];
        }
    }

    return ret;
}

void Context::terminal_strategy(System& s, C_Polyhedron* dualp) {
    // compute a new transition relation for each terminal

    int index = get_multiplier_status();

    if (index == NO_UNRESOLVED_MULTIPLIER) {
        // now add the invariants and update dualp
        s.add_invariants_and_update(polyStore->getPolyRef(), (*dualp));
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
        clump.insert(polyStore->getPolyRef());
        return;  // nothing to be done
    }

    // now go though all the multipliers for which zero or one is forbidden and
    // apply the remaining choose 0/1 values for the multiplier and expand
    LinTransform lt(lambdaNum, lambdaInfo);
    Context* childClump;

    for (i = 0; i < lambdaNum; i++) {
        switch (tt[i]) {
            case ZERO_ONE_FORBIDDEN:
                continue;
            case ZERO_FORBIDDEN:
                lt[i] = 1;
                lt[lambdaNum] = -1;
                addTransform(lt);
                lt[i] = 0;
                lt[lambdaNum] = 0;

                break;

            case ONE_FORBIDDEN:
                lt[i] = 1;
                addTransform(lt);
                lt[i] = 0;
                break;

            default:
                break;
        }
    }
    simplify_repeat();
    index = get_multiplier_status();
    if (index == NO_UNRESOLVED_MULTIPLIER) {
        clump.insert(polyStore->getPolyRef());
        return;  // nothing to be done
    }
    // now split on the remaining cases
    for (i = 0; i < lambdaNum; i++) {
        if (tt[i] == ZERO_ONE_ALLOWED) {
            lt[i] = 1;
            lt[lambdaNum] = 0;
            childClump = this->clone();
            childClump->addTransform(lt);
            childClump->simplify_repeat();
            childClump->RecursiveSplit(clump);
            delete (childClump);

            lt[i] = 1;
            lt[lambdaNum] = Rational(-1, 1);
            childClump = this->clone();
            childClump->addTransform(lt);
            childClump->simplify_repeat();
            childClump->RecursiveSplit(clump);
            delete (childClump);

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

   PRECONDITION( result.space_dimension()== (unsigned) 2 * coefNum);

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
        (*dualp) = C_Polyhedron(coefNum, UNIVERSE);
        vector<Location*>::iterator it;
        for (it = loclist->begin(); it < loclist->end(); it++) {
            (*it)->extract_invariants_and_update(polyStore->getPolyRef(),
                                                 *dualp);
        }
        return;  // nothing to be done
    }

    // now go though all the multipliers for which zero or one is forbidden and
    // apply the remaining choose 0/1 values for the multiplier and expand
    LinTransform lt(lambdaNum, lambdaInfo);
    Context* childClump;

    for (i = 0; i < lambdaNum; i++) {
        switch (tt[i]) {
            case ZERO_ONE_FORBIDDEN:
                continue;
            case ZERO_FORBIDDEN:
                lt[i] = 1;
                lt[lambdaNum] = -1;
                addTransform(lt);
                lt[i] = 0;
                lt[lambdaNum] = 0;

                break;

            case ONE_FORBIDDEN:
                lt[i] = 1;
                addTransform(lt);
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
        (*dualp) = C_Polyhedron(coefNum, UNIVERSE);
        vector<Location*>::iterator it;
        for (it = loclist->begin(); it < loclist->end(); it++) {
            (*it)->extract_invariants_and_update(polyStore->getPolyRef(),
                                                 *dualp);
        }
        return;  // nothing to be done
    }
    // now split on the remaining cases
    for (i = 0; i < lambdaNum; i++) {
        if (tt[i] == ZERO_ONE_ALLOWED) {
            lt[i] = 1;
            childClump = this->clone();
            childClump->addTransform(lt);
            childClump->simplify_repeat();
            childClump->RecursiveSplit(loclist, dualp, wtime, timed, one_timer);
            delete (childClump);

            lt[i] = 1;
            lt[lambdaNum] = Rational(-1, 1);

            childClump = this->clone();
            childClump->addTransform(lt);
            childClump->simplify_repeat();
            childClump->RecursiveSplit(loclist, dualp, wtime, timed, one_timer);
            delete (childClump);

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
        polyStore->collect_generators(g);
    }
}

// Old version, StInG compiling under PPL 0.9 (05/03/2006)
/*
void Context::validate_generators(Generator_System & g){
   Generator_System g1=polyStore->minimized_generators(); // obtain the
minimized generators from the polystore Generator_System::const_iterator it;

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
        polyStore->minimized_generators();  // obtain the minimized generators
                                            // from the polystore
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
    // 1. replacing all the eqExprs and ineqExprs by transforms
    // 2. Insert them into a clone of the disequality store
    // 3. check the final disequality store for consistency

    DisequalityStore* ds1 =
        disequalStore->clone();  // clone the disequality store

    vector<Expression>::iterator it;
    for (it = eqExprs->begin(); it < eqExprs->end(); it++) {
        SparseLinExpr p((*it).to_transform(g));
        ds1->add_constraint(p, TYPE_EQ);
    }

    for (it = ineqExprs->begin(); it < ineqExprs->end(); it++) {
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
    delete (equalStore);
    delete (polyStore);
    delete (disequalStore);
    delete (eqExprs);
    delete (ineqExprs);
    delete (factors);
}

void Context::obtain_primal_polyhedron(int left, C_Polyhedron& result) {
    PRECONDITION((result.space_dimension() == (unsigned)varsNum),
                 " Polyhedron of wrong space dimension passed");

    PRECONDITION((left >= 0 && left + varsNum + 1 <= coefNum),
                 " Asked to primalize out of range");

    // assume that result's space dimension is =varsNum

    // obtain the generators of the polystore polyhedron
    reconcile_stores();
    C_Polyhedron const& pp = polyStore->get_nnc_poly_reference();
    Generator_System gs = pp.generators();
    // now make them into constraints
    Generator_System::const_iterator it;

    Linear_Expression ll;
    int i, j;
    for (it = gs.begin(); it != gs.end(); ++it) {
        ll *= 0;  // reset the linexpr
        for (i = 0; i < varsNum; ++i) {
            j = handle_integers((*it).coefficient(Variable(left + i)));
            ll += j * Variable(i);
        }

        ll += handle_integers((*it).coefficient(Variable(left + varsNum)));

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
    PRECONDITION((index >= 0 && index < lambdaNum),
                 " Context::is_multiplier_present() --- Index out of range");

    vector<Expression>::iterator it;
    for (it = eqExprs->begin(); it < eqExprs->end(); ++it) {
        if ((*it).is_multiplier_present(index))
            return true;
    }
    for (it = ineqExprs->begin(); it < ineqExprs->end(); ++it) {
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
    // range [left.. left+varsNum] or else this will not work
    //

    PRECONDITION((result.space_dimension() == (unsigned)(2 * varsNum)),
                 " result polyhedron not of the correct space dimension");

    PRECONDITION((left >= 0 && left + varsNum + 1 <= coefNum),
                 " Context::obtain_transtion_relation -- left1 out of range");

    //
    // first create a polyhedron called temp in which constraints on \mu
    // also check if the polyhedron satisfies the constraints above
    //

    C_Polyhedron temp(2 * varsNum + 2, UNIVERSE);
    Linear_Expression ll;

    // vector<Expression>::iterator it;

    // first handle the equalities

    bool res1 = to_constraints_(mult_index, left, temp, eqExprs, false);

    if (!res1) {
        // something went wrong
        return false;
    }

    // inequalities

    res1 = to_constraints_(mult_index, left, temp, ineqExprs, true);

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
        for (i = 0; i < varsNum; i++) {
            j = -handle_integers((*vgs).coefficient(Variable(i)));
            ll += j * Variable(i);
        }

        j = -handle_integers((*vgs).coefficient(Variable(varsNum)));
        ll += j;
        for (i = 0; i < varsNum; i++) {
            j = handle_integers((*vgs).coefficient(Variable(varsNum + 1 + i)));
            ll += j * Variable(varsNum + i);
        }
        j = handle_integers((*vgs).coefficient(Variable(2 * varsNum + 1)));
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

        for (i = left + varsNum + 1; i < coefNum; ++i)
            if (mc(i) != 0)
                return false;

        // now obtain fill in the constraints for muc
        for (i = 0; i <= varsNum; ++i) {
            j = mc(i + left).num();

            ll += j * Variable(i);
        }

        mc = (*it)(lambdaNum);

        for (i = 0; i < left; ++i)
            if (mc(i) != 0)
                return false;

        for (i = left + varsNum + 1; i < coefNum; ++i)
            if (mc(i) != 0)
                return false;

        // now obtain fill in the constraints for c
        for (i = 0; i <= varsNum; ++i) {
            j = mc(i + left).num();

            ll += j * Variable(i + varsNum + 1);
        }
        if (ineq)
            result.add_constraint(ll >= 0);
        else
            result.add_constraint(ll == 0);
    }
    return true;
}
