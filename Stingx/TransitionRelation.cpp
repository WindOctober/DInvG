
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

#include "TransitionRelation.h"

#include "Elimination.h"
#include "Macro.h"
#include "PolyUtils.h"
#include "myassertions.h"

extern bool zero;
extern bool one;
extern bool falsepath;
extern bool trsat;
extern bool noexitpath;
extern int debug_2, debug_3;

void TransitionRelation::initialize(int vars_num,
                                    var_info* info,
                                    var_info* dual_info,
                                    var_info* lambda_info,
                                    Location* preloc,
                                    Location* postloc,
                                    C_Polyhedron* rel,
                                    string name) {
    this->vars_num = vars_num;
    this->info = info;
    fp = info->prime();
    this->dual_info = dual_info;

    this->lambda_info = lambda_info;
    this->preloc = preloc;
    this->postloc = postloc;
    this->trans_poly = rel;
    this->name = name;
    populate_multipliers();
    fired = 0;

    guard = new C_Polyhedron(vars_num, UNIVERSE);
    update = new C_Polyhedron(2 * vars_num, UNIVERSE);
}

void TransitionRelation::initialize(int vars_num,
                                    var_info* info,
                                    var_info* dual_info,
                                    var_info* lambda_info,
                                    string name) {
    this->vars_num = vars_num;
    this->info = info;
    fp = info->prime();
    this->dual_info = dual_info;

    this->lambda_info = lambda_info;

    this->name = name;
    populate_multipliers();
    fired = 0;

    guard = new C_Polyhedron(vars_num, UNIVERSE);
    update = new C_Polyhedron(2 * vars_num, UNIVERSE);
}

void TransitionRelation::initialize_without_populating(int vars_num,
                                                       var_info* info,
                                                       var_info* dual_info,
                                                       var_info* lambda_info,
                                                       Location* preloc,
                                                       Location* postloc,
                                                       C_Polyhedron* rel,
                                                       string name,
                                                       int index) {
    this->vars_num = vars_num;
    this->info = info;
    fp = info->prime();
    this->dual_info = dual_info;

    this->lambda_info = lambda_info;
    this->preloc = preloc;
    this->postloc = postloc;
    this->trans_poly = rel;
    this->name = name;
    this->index = index;
    fired = 0;

    guard = new C_Polyhedron(vars_num, UNIVERSE);
    update = new C_Polyhedron(2 * vars_num, UNIVERSE);
}

void TransitionRelation::initialize_without_populating(int vars_num,
                                                       var_info* info,
                                                       var_info* dual_info,
                                                       var_info* lambda_info,
                                                       string name,
                                                       int index) {
    this->vars_num = vars_num;
    this->info = info;
    fp = info->prime();
    this->dual_info = dual_info;

    this->lambda_info = lambda_info;
    this->index = index;
    this->name = name;
    fired = 0;

    guard = new C_Polyhedron(vars_num, UNIVERSE);
    update = new C_Polyhedron(2 * vars_num, UNIVERSE);
}

// The function checks whether the constraint includes primed variables. If it
// does not include primed variables, it is considered as a guard.
bool TransitionRelation::add_guard(Constraint const& constraint) {
    int res;
    bool flag = true;
    // make sure the coefficients of primed part is zero.
    for (int i = vars_num; i < 2 * vars_num; ++i) {
        flag = handle_integers(constraint.coefficient(Variable(i)), res);
        if (res != 0 || !flag)
            return false;
    }

    flag = handle_integers(constraint.inhomogeneous_term(), res);

    Linear_Expression ll(res);

    for (int i = 0; i < vars_num; ++i) {
        flag &= handle_integers(constraint.coefficient(Variable(i)), res);
        ll += res * Variable(i);
    }
    if (flag) {
        if (constraint.is_equality()) {
            guard->add_constraint(ll == 0);
        } else if (constraint.is_nonstrict_inequality()) {
            guard->add_constraint(ll >= 0);
        } else {
            guard->add_constraint(ll > 0);
        }
    }
    return flag;
}

// The function checks whether a specific constraint is in the form of x' = x
// and records the variables in this form.
bool TransitionRelation::add_preservation_relation(Constraint const& cc) {
    int pres = -1;
    int coef, primed_coef;
    bool flag = true;
    if (!cc.is_equality())
        return false;
    flag = handle_integers(cc.inhomogeneous_term(), coef);

    if (!flag || coef != 0)
        return false;

    for (int i = 0; i < vars_num; ++i) {
        flag &= handle_integers(cc.coefficient(Variable(i)), coef);
        flag &= handle_integers(cc.coefficient(Variable(i + vars_num)), primed_coef);
        if (!flag)
            return false;
        if (coef == 0 && primed_coef == 0)
            continue;

        if (coef + primed_coef == 0 && pres == -1) {
            pres = i;
            continue;
        }
        return false;
    }

    if (pres == -1)
        return false;

    preserved.insert(pres);
    return true;
}

bool TransitionRelation::split_relation() {
    Constraint_System cs = trans_poly->minimized_constraints();

    for (auto vi = cs.begin(); vi != cs.end(); ++vi) {
        if (add_guard((*vi)) || add_preservation_relation((*vi)))
            continue;
        update->add_constraint((*vi));
    }

    return true;
}

bool TransitionRelation::is_preserved(int i) const {
    if (preserved.find(i) == preserved.end())
        return false;
    return true;
}

void TransitionRelation::compute_post_new(const C_Polyhedron* p,
                                          C_Polyhedron& q) const {
    q = *p;

    //
    // q is a vars_num dimensional polyhedron for which one needs to
    // compute the post operation
    //

    q.intersection_assign((*guard));

    if (q.is_empty())
        return;

    q.add_space_dimensions_and_embed(vars_num);

    // now transform q for each preserved relation
    set<int>::iterator vi;

    for (vi = preserved.begin(); vi != preserved.end(); ++vi) {
        Linear_Expression ll = Variable((*vi));
        q.affine_image(Variable((*vi) + vars_num), ll);  // transforming
                                                  // each preserved relation
    }

    q.intersection_assign((*update));

    Variables_Set vs;

    int i;
    for (i = 0; i < vars_num; i++) {
        vs.insert(Variable(i));
    }
    q.remove_space_dimensions(vs);
}

void TransitionRelation::set_locs(Location* preloc, Location* postloc) {
    this->preloc = preloc;
    this->postloc = postloc;
}
void TransitionRelation::set_relation(C_Polyhedron* rel) {
    this->trans_poly = rel;
    compute_nc();
    split_relation();
}

void TransitionRelation::compute_nc() {
    Constraint_System cs = trans_poly->minimized_constraints();
    Constraint_System::const_iterator vi;
    string str;
    constraints_num = 0;

    for (vi = cs.begin(); vi != cs.end(); ++vi)
        constraints_num++;
}

TransitionRelation::TransitionRelation(int vars_num,
                                       var_info* info,
                                       var_info* dual_info,
                                       var_info* lambda_info,
                                       string name) {
    initialize(vars_num, info, dual_info, lambda_info, name);
}

TransitionRelation::TransitionRelation(int vars_num,
                                       var_info* info,
                                       var_info* dual_info,
                                       var_info* lambda_info,
                                       Location* preloc,
                                       Location* postloc,
                                       C_Polyhedron* rel,
                                       string name) {
    initialize(vars_num, info, dual_info, lambda_info, preloc, postloc, rel, name);
}

TransitionRelation::TransitionRelation(int vars_num,
                                       var_info* info,
                                       var_info* dual_info,
                                       var_info* lambda_info,
                                       string name,
                                       int index) {
    initialize_without_populating(vars_num, info, dual_info, lambda_info, name, index);
}

TransitionRelation::TransitionRelation(int vars_num,
                                       var_info* info,
                                       var_info* dual_info,
                                       var_info* lambda_info,
                                       Location* preloc,
                                       Location* postloc,
                                       C_Polyhedron* rel,
                                       string name,
                                       int index) {
    initialize_without_populating(vars_num, info, dual_info, lambda_info, preloc, postloc, rel, name,
                                  index);
}

void TransitionRelation::strengthen(const C_Polyhedron* p) {
    guard->intersection_assign(*p);  // update the guard

    C_Polyhedron* q = new C_Polyhedron(*p);
    q->add_space_dimensions_and_embed(vars_num);
    trans_poly->intersection_assign(*q);
    delete (q);

    compute_nc();
    split_relation();
}

void TransitionRelation::compute_post(const C_Polyhedron* p,
                                      C_Polyhedron& q) const {
    // assume that q=*p
    q = *p;

    q.add_space_dimensions_and_embed(vars_num);

    q.intersection_assign(*trans_poly);

    Variables_Set vs;

    int i;
    for (i = 0; i < vars_num; i++)
        vs.insert(Variable(i));

    q.remove_space_dimensions(vs);
}

/*
TransitionRelation * TransitionRelation::compose(TransitionRelation * t){
  // not implemented for the time being
}

*/

void TransitionRelation::compute_consecution_constraints(Context& context) {
    // Use two expression stores. One for the equations and
    // the other for the inequations
    cout << endl;
    cout << endl
         << "> > > (intra transition) In compute_consecution_constraints(), "
            "TransitionRelation : "
         << name;
    Clump* preloc_d_cl = preloc->get_d_cl();
    bool legal_trans = true;
    cout << endl << "Current transition has poly as follows: ";
    cout << endl << "  " << *trans_poly;

    // if transition has false-relation, then ignore it
    // (trsat==true) means that opening the verification for transition-sat
    if (trsat) {
        if (trans_poly->is_empty()) {
            legal_trans = false;
        }
    }
    cout << endl << "  Compute this transition: " << legal_trans;

    if (legal_trans) {
        int lambda_num = lambda_info->get_dimension();
        int dual_num = dual_info->get_dimension();
        Constraint_System cs = trans_poly->minimized_constraints();
        Constraint_System cs_dis;
        Constraint_System::const_iterator it;
        int l1 = preloc->get_range_left(), l2 = postloc->get_range_left();
        int i, j;
        C_Polyhedron enable_poly(2 * vars_num + 2 + constraints_num, UNIVERSE);
        C_Polyhedron disable_poly(2 * vars_num + 2 + constraints_num, UNIVERSE);
        int offset = vars_num + 1, primed_offset = 2 * vars_num + 2;
        Linear_Expression expr(0);

        // (1) first the constraints on the unprimed variables
        for (i = 0; i < vars_num; i++) {
            expr = Variable(i);  // place holder for \mu * c_i
            j = 0;
            for (it = cs.begin(); it != cs.end(); it++) {
                expr += handle_integers((*it).coefficient(Variable(i))) * Variable(primed_offset + j);  // coefficient for \lambda_j
                j++;
            }
            enable_poly.add_constraint(expr == 0);
            disable_poly.add_constraint( expr == 0);

        }

        // (2) constraints on the primed variable
        for (i = 0; i < vars_num; i++) {
            expr = -1 * Variable(offset + i);  // - c_postloc_i
            j = 0;
            for (it = cs.begin(); it != cs.end(); it++) {
                expr += handle_integers((*it).coefficient(Variable(vars_num + i))) *
                      Variable(primed_offset + j);
                j++;
            }

            enable_poly.add_constraint(expr == 0);
        }
        for (i = 0; i < vars_num; i++) {
            expr = Linear_Expression(0);
            j = 0;
            for (it = cs.begin(); it != cs.end(); it++) {
                expr += handle_integers((*it).coefficient(Variable(vars_num + i))) *
                      Variable(primed_offset + j);
                j++;
            }
            // polyd.add_constraint_and_minimize(ll==0);
            disable_poly.add_constraint(expr == 0);
        }

        // (3) Constraints on the constant variable
        expr = Variable(vars_num);
        j = 0;
        for (it = cs.begin(); it != cs.end(); it++) {
            expr += handle_integers((*it).inhomogeneous_term()) *
                  Variable(primed_offset + j);
            j++;
        }
        disable_poly.add_constraint( expr <= -1);
        expr -= Variable(offset + vars_num);
        enable_poly.add_constraint(expr <= 0);

        // (4) Now for the positivity constraint (or \lambda >= 0 or \forall
        // \lambda)
        j = 0;
        for (it = cs.begin(); it != cs.end(); ++it) {
            if ((*it).type() == Constraint::NONSTRICT_INEQUALITY) {
                enable_poly.add_constraint(Variable(primed_offset + j) >= 0);
                disable_poly.add_constraint(Variable(primed_offset + j) >= 0);  
            } 
            else if ((*it).type() == Constraint::STRICT_INEQUALITY) {
                cerr << "Location::compute_dual_constraints -- Warning: "
                        "Encountered "
                        "Strict Inequality"
                     << endl;
                cerr << "                " << (*it) << endl;
                enable_poly.add_constraint(Variable(primed_offset + j) > 0);
                disable_poly.add_constraint(Variable(primed_offset + j) > 0); 
            }
            j++;
        }

        // contains_test(polyd, 2*vars_num+2);
        //  * * *
        //  Old method for eliminate lambda
        enable_poly.remove_higher_space_dimensions(2 * vars_num + 2);
        disable_poly.remove_higher_space_dimensions(2 * vars_num + 2);
        // * * *
        // * * *
        // New method for eliminate lambda: Farkas' Lemma 2.5a, Ax<=b
        // eliminate_by_Farkas(polyd, 2*vars_num+2);
        // * * *

        // now populate the context
        cs = enable_poly.minimized_constraints();
        cs_dis = disable_poly.minimized_constraints();

        Expression e(dual_num, lambda_num, dual_info, lambda_info);
        C_Polyhedron pdis1(dual_num, UNIVERSE);
        LinExpr ll1(dual_num, dual_info);
        for (it = cs.begin(); it != cs.end(); ++it) {
            for (i = 0; i <= vars_num; i++)
                e[index].set_coefficient(
                    l1 + i, handle_integers((*it).coefficient(Variable(i))));

            for (i = 0; i <= vars_num; i++)
                e[lambda_num].set_coefficient(
                    l2 + i,
                    handle_integers((*it).coefficient(Variable(offset + i))));

            if ((*it).is_inequality())
                context.add_inequality_expression(Expression(e));
            else if ((*it).is_equality())
                context.add_equality_expression(Expression(e));
        }
        if (falsepath) {
            // mu=1 in disabled path
            ll1 *= 0;

            for (it = cs_dis.begin(); it != cs_dis.end(); ++it) {
                ll1 *= 0;
                for (i = 0; i <= vars_num; i++)
                    ll1[l1 + i] =
                        handle_integers((*it).coefficient(Variable(i)));

                ll1[dual_num] = handle_integers((*it).inhomogeneous_term());
                if ((*it).is_inequality())
                    pdis1.add_constraint((ll1.to_lin_expression()) >= 0);
                else if ((*it).is_equality())
                    pdis1.add_constraint((ll1.to_lin_expression()) == 0);
            }
            preloc_d_cl->insert(pdis1);
        }
        cout << endl
             << "  pushing back clump with " << preloc_d_cl->get_count()
             << " Polyhedra (in falsepath)...";
    }

    cout << endl
         << "< < < Intra-Transition::" << name
         << " prepare to push back clump with " << preloc_d_cl->get_count()
         << " Polyhedra";
}

void TransitionRelation::compute_consecution_01(vector<Clump>& clumps) {
    cout << endl;
    cout << endl
         << "> > > (inter transition) In compute_consecution_01(), "
            "TransitionRelation : "
         << name;
    Clump cl(dual_info, name, "Transition");
    bool compute_this_trans = true;
    cout << endl << "Current transition has poly as follows: ";
    cout << endl << "  " << *trans_poly;

    // if transition has false-relation, then ignore it
    // (trsat==true) means that opening the verification for transition-sat
    if (trsat) {
        if (trans_poly->is_empty()) {
            compute_this_trans = false;
        }
    }
    // if transition points to exit-location, then ignore it
    // (noexitpath==true) means ignore the exit-transition
    if (noexitpath) {
        if (get_postloc_name() == EXIT_LOCATION) {
            compute_this_trans = false;
        }
    }
    cout << endl << "  Compute this transition: " << compute_this_trans;

    if (compute_this_trans) {
        Constraint_System cs, cs_dis;
        Constraint_System::const_iterator vi;
        int dual_num = dual_info->get_dimension();
        cs = trans_poly->minimized_constraints();
        int l1 = preloc->get_range_left(), l2 = postloc->get_range_left();
        int i, j;
        C_Polyhedron polyd(2 * vars_num + 2 + constraints_num, UNIVERSE);
        C_Polyhedron polyd_dis(2 * vars_num + 2 + constraints_num, UNIVERSE);
        int offset1 = vars_num + 1, offset2 = 2 * vars_num + 2;
        Linear_Expression ll(0);
        if (debug_3) {
            cout << endl << "------------------------------";
            cout << endl << "- dual_num: " << dual_num;
            cout << endl << "- vars_num: " << vars_num;
            cout << endl << "- l1: " << l1;
            cout << endl << "- l2: " << l2;
            cout << endl << "- offset1: " << offset1;
            cout << endl << "- offset2: " << offset2;
        }

        // (1) first the constraints on the unprimed variables
        for (i = 0; i < vars_num; i++) {
            ll = Variable(i);  // place holder for \mu * c_i
            j = 0;
            for (vi = cs.begin(); vi != cs.end(); vi++) {
                ll += handle_integers((*vi).coefficient(Variable(i))) *
                      Variable(offset2 + j);  // coefficient for \lambda_j
                j++;
            }
            // polyd.add_constraint_and_minimize(ll==0);
            polyd.add_constraint(ll == 0);
            polyd_dis.add_constraint(
                ll == 0);  // disabled path; added by Hongming, at
                           // Shanghai Jiao Tong University, 2022/09/13
        }

        // (2) constraints on the primed variable
        for (i = 0; i < vars_num; i++) {
            ll = -1 * Variable(offset1 + i);  // - c_postloc_i
            j = 0;
            for (vi = cs.begin(); vi != cs.end(); vi++) {
                ll += handle_integers((*vi).coefficient(Variable(vars_num + i))) *
                      Variable(offset2 + j);  // coefficient for \lambda_j
                j++;
            }
            // polyd.add_constraint_and_minimize(ll==0);
            polyd.add_constraint(ll == 0);
        }
        for (i = 0; i < vars_num; i++) {
            // disabled path; added by Hongming, at Shanghai Jiao Tong
            // University, 2022/09/13
            ll = Linear_Expression(0);
            j = 0;
            for (vi = cs.begin(); vi != cs.end(); vi++) {
                ll += handle_integers((*vi).coefficient(Variable(vars_num + i))) *
                      Variable(offset2 + j);  // coefficient for \lambda_j
                j++;
            }
            // polyd.add_constraint_and_minimize(ll==0);
            polyd_dis.add_constraint(ll == 0);
        }
        
        // (3) Constraints on the constant variable
        ll = -Variable(vars_num);  // -M * d_preloc
        j = 0;
        for (vi = cs.begin(); vi != cs.end(); vi++) {
            ll += -handle_integers((*vi).inhomogeneous_term()) *
                  Variable(offset2 + j);  // -coefficient for \lambda_j
            j++;
        }
        polyd_dis.add_constraint(
            ll >= 1);  // disabled path; added by Hongming, at
                       // Shanghai Jiao Tong University, 2022/09/13
        ll += Variable(offset1 + vars_num);  // + d_postloc
        // polyd.add_constraint_and_minimize(ll>=0);
        polyd.add_constraint(ll >= 0);

        // (4) Now for the positivity constraint (or \lambda >= 0 or \forall
        // \lambda)
        j = 0;
        for (vi = cs.begin(); vi != cs.end(); ++vi) {
            if ((*vi).type() == Constraint::NONSTRICT_INEQUALITY) {
                // polyd.add_constraint_and_minimize(Variable(offset2+j)>=0);
                polyd.add_constraint(Variable(offset2 + j) >= 0);
                polyd_dis.add_constraint(
                    Variable(offset2 + j) >=
                    0);  // disabled path; added by Hongming, at Shanghai Jiao
                         // Tong University, 2022/09/13
            } else if ((*vi).type() == Constraint::STRICT_INEQUALITY) {
                cerr << "Location::compute_dual_constraints -- Warning: "
                        "Encountered "
                        "Strict Inequality"
                     << endl;
                cerr << "                " << (*vi) << endl;
                // polyd.add_constraint_and_minimize(Variable(offset2+j)>0);
                polyd.add_constraint(Variable(offset2 + j) > 0);
                polyd_dis.add_constraint(
                    Variable(offset2 + j) >
                    0);  // disabled path; added by Hongming, at Shanghai Jiao
                         // Tong University, 2022/09/13
            }
            j++;
        }

        if (debug_2) {
            cout << endl << "------------------------------";
            cout << endl
                 << "- polyd_dis(with \\lambda): " << endl
                 << "  " << polyd_dis;
        }
        // contains_test(polyd, 2*vars_num+2);
        // Timer test_time_for_remove_higher_space_dimensions;
        //  * * *
        //  Old method for eliminate lambda
        polyd.remove_higher_space_dimensions(2 * vars_num + 2);
        polyd_dis.remove_higher_space_dimensions(2 * vars_num + 2);
        // * * *
        // * * *
        // New method for eliminate lambda: Farkas' Lemma 2.5a, Ax<=b
        // eliminate_by_Farkas(polyd, 2*vars_num+2);
        // eliminate_by_Farkas(polyd_dis, 2*vars_num+2);
        // * * *
        // test_time_for_remove_higher_space_dimensions.stop();
        // cout<<endl<<"- The remove_higher_space_dimensions(in inter location)
        // Time Taken is :
        // "<<test_time_for_remove_higher_space_dimensions.compute_time_elapsed()<<endl;


        // now create two input polyhedra
        cs = polyd.minimized_constraints();
        cs_dis =
            polyd_dis.minimized_constraints();  // disabled path; added by
                                                // Hongming, at Shanghai Jiao
                                                // Tong University, 2022/09/13
        if (debug_2) {
            cout << endl
                 << "- cs_dis(projected away \\lambda): " << endl
                 << "  " << cs_dis;
        }
        C_Polyhedron p0(dual_num, UNIVERSE), p1(dual_num, UNIVERSE), pdis0(dual_num, UNIVERSE),
            pdis1(dual_num, UNIVERSE);
        // Expression e(dual_num,r,dual_info,lambda_info);
        LinExpr ll1(dual_num, dual_info);
        if (one) {
            // mu=1
            for (vi = cs.begin(); vi != cs.end(); ++vi) {
                for (i = 0; i <= vars_num; i++)
                    ll1[l1 + i] =
                        handle_integers((*vi).coefficient(Variable(i)));
                for (i = 0; i <= vars_num; i++)
                    ll1[l2 + i] = handle_integers(
                        (*vi).coefficient(Variable(offset1 + i)));
                if ((*vi).is_inequality())
                    // p1.add_constraint_and_minimize((ll1.to_lin_expression())
                    // >= 0);
                    p1.add_constraint((ll1.to_lin_expression()) >= 0);
                else if ((*vi).is_equality())
                    // p1.add_constraint_and_minimize((ll1.to_lin_expression())
                    // == 0);
                    p1.add_constraint((ll1.to_lin_expression()) == 0);
            }
            cl.insert(p1);
            if (debug_2) {
                cout << endl << "------------------------------";
                cout << endl
                     << "- p1(mu=1 in enabled path): " << endl
                     << "  " << p1;
            }
        }
        cout << endl
             << "  pushing back clump with " << cl.get_count()
             << " Polyhedra...";
        if (zero) {
            // mu=0
            ll1 *= 0;
            for (vi = cs.begin(); vi != cs.end(); ++vi) {
                for (i = 0; i <= vars_num; i++)
                    ll1[l2 + i] = handle_integers(
                        (*vi).coefficient(Variable(offset1 + i)));
                if ((*vi).is_inequality())
                    // p0.add_constraint_and_minimize((ll1.to_lin_expression())
                    // >= 0);
                    p0.add_constraint((ll1.to_lin_expression()) >= 0);
                else if ((*vi).is_equality())
                    // p0.add_constraint_and_minimize((ll1.to_lin_expression())
                    // == 0);
                    p0.add_constraint((ll1.to_lin_expression()) == 0);
            }
            cl.insert(p0);
        }
        cout << endl
             << "  pushing back clump with " << cl.get_count()
             << " Polyhedra...";
        if (falsepath) {
            // mu=1 in disabled path
            ll1 *= 0;
            for (vi = cs_dis.begin(); vi != cs_dis.end(); ++vi) {
                ll1 *= 0;
                if (debug_2) {
                    cout << endl
                         << "- vi=cs_dis.begin()~end(): " << endl
                         << "  " << (*vi);
                }
                for (i = 0; i <= vars_num; i++)
                    ll1[l1 + i] =
                        handle_integers((*vi).coefficient(Variable(i)));
                for (i = 0; i <= vars_num; i++)
                    ll1[l2 + i] = handle_integers(
                        (*vi).coefficient(Variable(offset1 + i)));
                ll1[dual_num] = handle_integers((*vi).inhomogeneous_term());
                if ((*vi).is_inequality())
                    pdis1.add_constraint((ll1.to_lin_expression()) >= 0);
                else if ((*vi).is_equality())
                    pdis1.add_constraint((ll1.to_lin_expression()) == 0);
                if (debug_2) {
                    cout << endl << "  ll1: " << endl << "  " << ll1;
                    if ((*vi).is_inequality()) {
                        cout << " >= 0 ";
                    } else if ((*vi).is_equality()) {
                        cout << " == 0 ";
                    }
                }
            }
            cl.insert(pdis1);
            if (debug_2) {
                cout << endl
                     << "- pdis1(mu=1 in disabled path): " << endl
                     << "  " << pdis1;
            }
        }
        cout << endl
             << "  pushing back clump with " << cl.get_count()
             << " Polyhedra (in falsepath)...";
        /* "mu=0 in disabled path" is trivial
        if (1){
        // mu=0 in disabled path
           ll1*=0;
           for (vi=cs_dis.begin();vi!=cs_dis.end();++vi){
              for(i=0;i<=vars_num;i++)
                 ll1[l2+i]=handle_integers((*vi).coefficient(Variable(offset1+i)));
              if ((*vi).is_inequality())
                 pdis0.add_constraint((ll1.to_lin_expression()) >= 0);
              else if ((*vi).is_equality())
                 pdis0.add_constraint((ll1.to_lin_expression()) == 0);
           }
           cl.insert(pdis0);
        }
        cout<<endl<<" pushing back clump with "<<cl.get_count()<<"
        Polyhedra...";
        */
    }
    cout << endl
         << "< < < Inter-Transition::" << name << " pushing back clump with "
         << cl.get_count() << " Polyhedra...";
    if (cl.get_count() != 0) {
        clumps.push_back(cl);
    }
    cout << "done";

    return;
}

void TransitionRelation::compute_consecution_constraints(vector<Clump>& vcl,
                                                         C_Polyhedron& init_poly) {
    // First make up a context and add the initiation constraints to it
    if (preloc->get_name() != postloc->get_name()) {
        compute_consecution_01(vcl);
        return;
    }
    Context* cc = preloc->get_context();
    compute_consecution_constraints(*cc);
    return;
}

void TransitionRelation::populate_multipliers() {
    index = lambda_info->get_dimension();
    string str = "M_" + name;
    lambda_info->insert(str.c_str());
}

int TransitionRelation::get_range_left() const {
    return mult_left;
}

int TransitionRelation::get_range_right() const {
    return mult_right;
}

const string& TransitionRelation::get_name() const {
    return name;
}

const string& TransitionRelation::get_preloc_name() const {
    return preloc->get_name();
}

const string& TransitionRelation::get_postloc_name() const {
    return postloc->get_name();
}

const C_Polyhedron& TransitionRelation::get_relation() const {
    return *trans_poly;
}

const var_info* TransitionRelation::get_varinfo() const {
    return fp;
}

ostream& operator<<(ostream& in, TransitionRelation const& t) {
    // Just print the transition relation
    var_info const* ff = t.get_varinfo();

    in << "Transition Relation: " << t.get_name() << endl;
    in << "Pre-Location:" << t.get_preloc_name() << "  "
       << " Post-Location:" << t.get_postloc_name() << endl;
    in << "Transition Relation: [[" << endl;
    in << "| " << endl;
    print_polyhedron(in, t.get_relation(), ff);
    in << "| " << endl;
    in << "]]" << endl;
    in << "Guard: [[" << endl;
    in << "| " << endl;
    print_polyhedron(in, t.get_guard_poly(), ff);
    in << "| " << endl;
    in << "]]" << endl;
    in << "Update: [[" << endl;
    in << "| " << endl;
    print_polyhedron(in, t.get_update_poly(), ff);
    in << "| " << endl;
    in << "]]" << endl;
    in << "Preserved: [[" << endl;
    in << "| " << endl;
    set<int> const& st = t.get_preserved_set();
    set<int>::iterator vxx;
    for (vxx = st.begin(); vxx != st.end(); ++vxx) {
        in << "├ ";
        in << " " << ff->get_name((*vxx)) << endl;
    }
    in << "| " << endl;
    in << "]]" << endl;
    in << endl;
    in << "- Transition Relation " << t.get_name() << " Ends" << endl;
    in << "----------------------------- " << endl;
    return in;
}

bool TransitionRelation::matches(string& nam) const {
    return (name == nam);
}

bool TransitionRelation::fire() {
    if (!preloc->has_initial()) {
        return false;
    }
    C_Polyhedron* pre_p = preloc->get_initial();
    C_Polyhedron post_p(vars_num, UNIVERSE);
    compute_post_new(pre_p, post_p);

    postloc->set_polyhedron(&post_p);

    fired++;
    return true;
}

int TransitionRelation::get_firing_count() {
    return fired;
}

void TransitionRelation::add_preloc_invariant() {
    C_Polyhedron temp(preloc->inv_poly_reference());
    guard->intersection_assign(temp);
    temp.add_space_dimensions_and_embed(vars_num);
    trans_poly->intersection_assign(temp);
    compute_nc();
    return;
}

void TransitionRelation::dualize_standard(C_Polyhedron& result) const {
    result = C_Polyhedron(2 * vars_num + 2 + constraints_num, UNIVERSE);
    Constraint_System cs = trans_poly->minimized_constraints();
    Constraint_System::const_iterator vi;
    bool flag = true;
    int i;
    int j, k;

    //
    // dualize & build the constraints
    // \rho \models c_1 x_1 + ... + c_{vars_num+2} x_1' + .. + c_{2n+1} x_n' + c_{vars_num+1}
    // + c_{2n+2} >=0
    //

    for (i = 0; i < vars_num; ++i) {
        Linear_Expression ll;
        ll += -1 * Variable(i);
        flag = true;
        for (k = 0, vi = cs.begin(); vi != cs.end(); ++k, ++vi) {
            flag &= handle_integers((*vi).coefficient(Variable(i)), j);
            ll += j * Variable(2 * vars_num + 2 + k);
        }
        INVARIANT(flag,
                  " Fatal overflow in TransitionRelation::dualize_standard ");

        result.add_constraint(ll == 0);
    }

    for (i = vars_num + 1; i < 2 * vars_num + 1; ++i) {
        Linear_Expression ll;
        ll += -1 * Variable(i);
        flag = true;
        for (k = 0, vi = cs.begin(); vi != cs.end(); ++k, ++vi) {
            flag &= handle_integers((*vi).coefficient(Variable(i - 1)), j);
            ll += j * Variable(2 * vars_num + 2 + k);
        }
        INVARIANT(flag,
                  " Fatal overflow in TransitionRelation::dualize_standard ");

        result.add_constraint(ll == 0);
    }

    // now for the constraint on the constant term
    Linear_Expression ll1;
    ll1 = -1 * Variable(vars_num) - Variable(2 * vars_num + 1);
    flag = true;
    for (k = 0, vi = cs.begin(); vi != cs.end(); ++k, ++vi) {
        flag &= handle_integers((*vi).inhomogeneous_term(), j);
        ll1 += j * Variable(2 * vars_num + 2 + k);
    }
    INVARIANT(flag, " Fatal overflow in TransitionRelation::dualize_standard ");

    result.add_constraint(ll1 <= 0);

    // now add the constraints on the multipliers
    for (k = 0, vi = cs.begin(); vi != cs.end(); ++vi, ++k) {
        if ((*vi).is_equality())
            continue;
        if ((*vi).is_nonstrict_inequality())
            result.add_constraint(Variable(2 * vars_num + 2 + k) >= 0);
        else
            result.add_constraint(Variable(2 * vars_num + 2 + k) > 0);
    }

    // project off the dimension..

    result.remove_higher_space_dimensions(2 * vars_num + 2);
    return;
}

void TransitionRelation::check_map() {
    C_Polyhedron& pre_invariant = preloc->invariant_reference();
    C_Polyhedron& post_invariant = postloc->invariant_reference();

    C_Polyhedron temp(vars_num, UNIVERSE);

    compute_post_new(&pre_invariant, temp);

    if (!post_invariant.contains(temp)) {
        cerr << " consecution failed for transition:" << *this << endl;
    }
    return;
}
