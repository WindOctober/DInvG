
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

void TransitionRelation::initialize(int n,
                                    var_info* f,
                                    var_info* fd,
                                    var_info* fm,
                                    Location* preloc,
                                    Location* postloc,
                                    C_Polyhedron* rel,
                                    string name) {
    this->n = n;
    this->f = f;
    fp = f->prime();
    this->fd = fd;

    this->fm = fm;
    this->preloc = preloc;
    this->postloc = postloc;
    this->rel = rel;
    this->name = name;
    populate_multipliers();
    fired = 0;

    guard = new C_Polyhedron(n, UNIVERSE);
    update = new C_Polyhedron(2 * n, UNIVERSE);
}

void TransitionRelation::initialize(int n,
                                    var_info* f,
                                    var_info* fd,
                                    var_info* fm,
                                    string name) {
    this->n = n;
    this->f = f;
    fp = f->prime();
    this->fd = fd;

    this->fm = fm;

    this->name = name;
    populate_multipliers();
    fired = 0;

    guard = new C_Polyhedron(n, UNIVERSE);
    update = new C_Polyhedron(2 * n, UNIVERSE);
}

void TransitionRelation::initialize_without_populating(int n,
                                                       var_info* f,
                                                       var_info* fd,
                                                       var_info* fm,
                                                       Location* preloc,
                                                       Location* postloc,
                                                       C_Polyhedron* rel,
                                                       string name,
                                                       int index) {
    this->n = n;
    this->f = f;
    fp = f->prime();
    this->fd = fd;

    this->fm = fm;
    this->preloc = preloc;
    this->postloc = postloc;
    this->rel = rel;
    this->name = name;
    this->index = index;
    fired = 0;

    guard = new C_Polyhedron(n, UNIVERSE);
    update = new C_Polyhedron(2 * n, UNIVERSE);
}

void TransitionRelation::initialize_without_populating(int n,
                                                       var_info* f,
                                                       var_info* fd,
                                                       var_info* fm,
                                                       string name,
                                                       int index) {
    this->n = n;
    this->f = f;
    fp = f->prime();
    this->fd = fd;

    this->fm = fm;
    this->index = index;
    this->name = name;
    fired = 0;

    guard = new C_Polyhedron(n, UNIVERSE);
    update = new C_Polyhedron(2 * n, UNIVERSE);
}

bool TransitionRelation::add_guard(Constraint const& ccs) {
    int i, j;
    bool flag = true;

    /*
     * Check that all the coefficients of the primed part are zero
     */

    for (i = n; i < 2 * n; ++i) {
        flag = handle_integers(ccs.coefficient(Variable(i)), j);
        if (j != 0 || !flag)
            return false;
    }

    /*
     * Add the constraints to the guard
     */

    flag = handle_integers(ccs.inhomogeneous_term(), j);

    // the use of flag captures overflows

    Linear_Expression ll(j);

    for (i = 0; i < n; ++i) {
        flag &= handle_integers(ccs.coefficient(Variable(i)), j);
        ll += j * Variable(i);
    }
    if (flag) {
        if (ccs.is_equality()) {
            guard->add_constraint(ll == 0);
        } else if (ccs.is_nonstrict_inequality()) {
            guard->add_constraint(ll >= 0);
        } else {
            guard->add_constraint(ll > 0);
        }
    }
    return flag;
}

bool TransitionRelation::add_preservation_relation(Constraint const& cc) {
    int pres = -1;
    int i, j, j1;
    bool flag = true;
    if (!cc.is_equality())
        return false;
    flag = handle_integers(cc.inhomogeneous_term(), j);

    if (!flag)
        return false;

    if (j != 0)
        return false;

    for (i = 0; i < n; ++i) {
        // Look at the coefficient of  i and i+n terms

        flag &= handle_integers(cc.coefficient(Variable(i)), j);
        flag &= handle_integers(cc.coefficient(Variable(i + n)), j1);
        // overflow?
        if (!flag)
            return false;
        // both are zero?
        if (j == 0 && j1 == 0)
            continue;

        // both are non-zero and I have not seen any other candidate so far?

        if ((j + j1 == 0) && pres == -1) {
            pres = i;
            continue;
        }
        // none of the above
        return false;
    }

    if (pres == -1)
        return false;

    preserved.insert(pres);
    return true;
}

bool TransitionRelation::split_relation() {
    Constraint_System cs = rel->minimized_constraints();

    // try to add it under guard if not
    // add it under preserved expressions
    // if not add it
    //

    Constraint_System::const_iterator vi;
    for (vi = cs.begin(); vi != cs.end(); ++vi) {
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
    // q is a n dimensional polyhedron for which one needs to
    // compute the post operation
    //

    q.intersection_assign((*guard));

    if (q.is_empty())
        return;

    q.add_space_dimensions_and_embed(n);

    // now transform q for each preserved relation
    set<int>::iterator vi;

    for (vi = preserved.begin(); vi != preserved.end(); ++vi) {
        Linear_Expression ll = Variable((*vi));
        q.affine_image(Variable((*vi) + n), ll);  // transforming
                                                  // each preserved relation
    }

    q.intersection_assign((*update));

    Variables_Set vs;

    int i;
    for (i = 0; i < n; i++) {
        vs.insert(Variable(i));
    }
    q.remove_space_dimensions(vs);
}

void TransitionRelation::set_locs(Location* preloc, Location* postloc) {
    this->preloc = preloc;
    this->postloc = postloc;
}
void TransitionRelation::set_relation(C_Polyhedron* rel) {
    this->rel = rel;
    compute_nc();
    split_relation();
}

void TransitionRelation::compute_nc() {
    Constraint_System cs = rel->minimized_constraints();
    Constraint_System::const_iterator vi;
    string str;
    nc = 0;

    for (vi = cs.begin(); vi != cs.end(); ++vi)
        nc++;
}

TransitionRelation::TransitionRelation(int n,
                                       var_info* f,
                                       var_info* fd,
                                       var_info* fm,
                                       string name) {
    initialize(n, f, fd, fm, name);
}

TransitionRelation::TransitionRelation(int n,
                                       var_info* f,
                                       var_info* fd,
                                       var_info* fm,
                                       Location* preloc,
                                       Location* postloc,
                                       C_Polyhedron* rel,
                                       string name) {
    initialize(n, f, fd, fm, preloc, postloc, rel, name);
}

TransitionRelation::TransitionRelation(int n,
                                       var_info* f,
                                       var_info* fd,
                                       var_info* fm,
                                       string name,
                                       int index) {
    initialize_without_populating(n, f, fd, fm, name, index);
}

TransitionRelation::TransitionRelation(int n,
                                       var_info* f,
                                       var_info* fd,
                                       var_info* fm,
                                       Location* preloc,
                                       Location* postloc,
                                       C_Polyhedron* rel,
                                       string name,
                                       int index) {
    initialize_without_populating(n, f, fd, fm, preloc, postloc, rel, name,
                                  index);
}

void TransitionRelation::strengthen(const C_Polyhedron* p) {
    guard->intersection_assign(*p);  // update the guard

    C_Polyhedron* q = new C_Polyhedron(*p);
    q->add_space_dimensions_and_embed(n);
    rel->intersection_assign(*q);
    delete (q);

    compute_nc();
    split_relation();
}

void TransitionRelation::compute_post(const C_Polyhedron* p,
                                      C_Polyhedron& q) const {
    // assume that q=*p
    q = *p;

    q.add_space_dimensions_and_embed(n);

    q.intersection_assign(*rel);

    Variables_Set vs;

    int i;
    for (i = 0; i < n; i++)
        vs.insert(Variable(i));

    q.remove_space_dimensions(vs);
}

/*
TransitionRelation * TransitionRelation::compose(TransitionRelation * t){
  // not implemented for the time being
}

*/

void TransitionRelation::compute_consecution_constraints(Context& c) {
    // Use two expression stores. One for the equations and
    // the other for the inequations
    cout << endl;
    cout << endl
         << "> > > (intra transition) In compute_consecution_constraints(), "
            "TransitionRelation : "
         << name;
    Clump* preloc_d_cl = preloc->get_d_cl();
    bool compute_this_trans = true;
    cout << endl << "Current transition has poly as follows: ";
    cout << endl << "  " << *rel;

    // if transition has false-relation, then ignore it
    // (trsat==true) means that opening the verification for transition-sat
    if (trsat) {
        if (rel->is_empty()) {
            compute_this_trans = false;
        }
    }
    cout << endl << "  Compute this transition: " << compute_this_trans;

    if (compute_this_trans) {
        int r = fm->get_dimension();  // the number of multiplier variables
        int nd = fd->get_dimension();
        Constraint_System cs = rel->minimized_constraints();
        Constraint_System cs_dis;
        Constraint_System::const_iterator vi;
        int l1 = preloc->get_range_left(), l2 = postloc->get_range_left();
        int i, j;
        C_Polyhedron polyd(2 * n + 2 + nc, UNIVERSE);
        C_Polyhedron polyd_dis(2 * n + 2 + nc, UNIVERSE);
        int offset1 = n + 1, offset2 = 2 * n + 2;
        Linear_Expression ll(0);
        if (debug_3) {
            cout << endl << "------------------------------";
            cout << endl << "- nd: " << nd;
            cout << endl << "- n: " << n;
            cout << endl << "- l1: " << l1;
            cout << endl << "- l2: " << l2;
            cout << endl << "- offset1: " << offset1;
            cout << endl << "- offset2: " << offset2;
        }

        if (debug_2) {
            cout << endl << "------------------------------";
            cout << endl << "- vi=cs.begin()~end(): ";
            for (vi = cs.begin(); vi != cs.end(); vi++) {
                cout << endl << "  " << (*vi);
            }
        }
        // (1) first the constraints on the unprimed variables
        for (i = 0; i < n; i++) {
            ll = Variable(i);  // place holder for \mu * c_i
            j = 0;
            for (vi = cs.begin(); vi != cs.end(); vi++) {
                ll += handle_integers((*vi).coefficient(Variable(i))) *
                      Variable(offset2 + j);  // coefficient for \lambda_j
                j++;
            }
            // cout<<endl<<"1. ll in ll==0 is : "<<endl<<ll<<endl;
            // polyd.add_constraint_and_minimize(ll==0);
            polyd.add_constraint(ll == 0);
            polyd_dis.add_constraint(
                ll == 0);  // disabled path; added by Hongming, at
                           // Shanghai Jiao Tong University, 2022/09/20
            if (debug_2) {
                cout << endl
                     << "- unprimed constraint(in polyd_dis): " << endl
                     << "  " << (ll == 0);
            }
        }

        // (2) constraints on the primed variable
        for (i = 0; i < n; i++) {
            ll = -1 * Variable(offset1 + i);  // - c_postloc_i
            j = 0;
            for (vi = cs.begin(); vi != cs.end(); vi++) {
                ll += handle_integers((*vi).coefficient(Variable(n + i))) *
                      Variable(offset2 + j);  // coefficient for \lambda_j
                j++;
            }
            // cout<<endl<<"2. ll in ll==0 is : "<<endl<<ll<<endl;
            // polyd.add_constraint_and_minimize(ll==0);
            polyd.add_constraint(ll == 0);
        }
        for (i = 0; i < n; i++) {
            // disabled path; added by Hongming, at Shanghai Jiao Tong
            // University, 2022/09/20
            ll = Linear_Expression(0);
            j = 0;
            for (vi = cs.begin(); vi != cs.end(); vi++) {
                ll += handle_integers((*vi).coefficient(Variable(n + i))) *
                      Variable(offset2 + j);  // coefficient for \lambda_j
                j++;
            }
            // polyd.add_constraint_and_minimize(ll==0);
            polyd_dis.add_constraint(ll == 0);
            if (debug_2) {
                cout << endl
                     << "- primed constraint(in polyd_dis): " << endl
                     << "  " << (ll == 0);
            }
        }

        // (3) Constraints on the constant variable
        ll = -Variable(n);  // -M * d_preloc
        j = 0;
        for (vi = cs.begin(); vi != cs.end(); vi++) {
            ll += -handle_integers((*vi).inhomogeneous_term()) *
                  Variable(offset2 + j);  // -coefficient for \lambda_j
            j++;
        }
        polyd_dis.add_constraint(
            ll >= 1);  // disabled path; added by Hongming, at
                       // Shanghai Jiao Tong University, 2022/09/20
        if (debug_2) {
            cout << endl
                 << "- constant constraint(in polyd_dis): " << endl
                 << "  " << (ll >= 1);
        }
        ll += Variable(offset1 + n);  // + d_preloc
        // cout<<endl<<"3. ll in ll>=0 is : "<<endl<<ll<<endl;
        // polyd.add_constraint_and_minimize(ll>=0) ;
        polyd.add_constraint(ll >= 0);

        // (4) Now for the positivity constraint (or \lambda >= 0 or \forall
        // \lambda)
        j = 0;
        for (vi = cs.begin(); vi != cs.end(); ++vi) {
            // cout<<endl<<"Am I ready to place '>=0' to lambda ? "<<endl;
            if ((*vi).type() == Constraint::NONSTRICT_INEQUALITY) {
                // cout<<endl<<"Constraint is Non-Strict inequality"<<endl;
                // cout<<endl<<"4. "<<endl<<Variable(offset2+j)<<">=0"<<endl;
                // polyd.add_constraint_and_minimize(Variable(offset2+j)>=0);
                polyd.add_constraint(Variable(offset2 + j) >= 0);
                polyd_dis.add_constraint(
                    Variable(offset2 + j) >=
                    0);  // disabled path; added by Hongming, at Shanghai Jiao
                         // Tong University, 2022/09/20
                if (debug_2) {
                    cout << endl
                         << "- positivity \\lambda constraint(in polyd_dis): "
                         << endl
                         << "  " << (Variable(offset2 + j) >= 0);
                }
            } else if ((*vi).type() == Constraint::STRICT_INEQUALITY) {
                // cout<<endl<<"Constraint is Strict inequality"<<endl;
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
                         // Tong University, 2022/09/20
                if (debug_2) {
                    cout << endl
                         << "- positivity \\lambda constraint(in polyd_dis): "
                         << endl
                         << "  " << (Variable(offset2 + j) > 0);
                }
            } else if ((*vi).type() == Constraint::EQUALITY) {
                // cout<<endl<<"Constraint is Equality"<<endl;
                // cout<<endl<<"5. "<<endl<<Variable(offset2+j)<<">=0"<<endl;
                // polyd.add_constraint(Variable(offset2+j)>=0);
            } else {
                // cout<<endl<<"Unknown Constraint !! "<<endl;
            }
            j++;
        }

        if (debug_2) {
            cout << endl << "------------------------------";
            cout << endl
                 << "- polyd_dis(with \\lambda): " << endl
                 << "  " << polyd_dis;
        }
        // contains_test(polyd, 2*n+2);
        // Timer test_time_for_remove_higher_space_dimensions;
        //  * * *
        //  Old method for eliminate lambda
        polyd.remove_higher_space_dimensions(2 * n + 2);
        polyd_dis.remove_higher_space_dimensions(
            2 * n + 2);  // disabled path; added by Hongming, at Shanghai Jiao
                         // Tong University, 2022/09/20
        // * * *
        // * * *
        // New method for eliminate lambda: Farkas' Lemma 2.5a, Ax<=b
        // eliminate_by_Farkas(polyd, 2*n+2);
        // * * *
        // test_time_for_remove_higher_space_dimensions.stop();
        // cout<<endl<<"- The remove_higher_space_dimensions(in intra location)
        // Time Taken is :
        // "<<test_time_for_remove_higher_space_dimensions.compute_time_elapsed()<<endl;
        if (debug_2) {
            cout << endl
                 << "- polyd_dis(projected away \\lambda): " << endl
                 << "  " << polyd_dis;
        }

        // now populate the context
        cs = polyd.minimized_constraints();
        cs_dis =
            polyd_dis.minimized_constraints();  // disabled path; added by
                                                // Hongming, at Shanghai Jiao
                                                // Tong University, 2022/09/20
        if (debug_2) {
            cout << endl
                 << "- cs_dis(projected away \\lambda): " << endl
                 << "  " << cs_dis;
        }
        Expression e(nd, r, fd, fm);
        C_Polyhedron pdis1(nd, UNIVERSE);
        LinExpr ll1(nd, fd);
        for (vi = cs.begin(); vi != cs.end(); ++vi) {
            for (i = 0; i <= n; i++)
                e[index].set_coefficient(
                    l1 + i, handle_integers((*vi).coefficient(Variable(i))));

            for (i = 0; i <= n; i++)
                e[r].set_coefficient(
                    l2 + i,
                    handle_integers((*vi).coefficient(Variable(offset1 + i))));

            if ((*vi).is_inequality())
                c.add_inequality_expression(Expression(e));
            else if ((*vi).is_equality())
                c.add_equality_expression(Expression(e));
        }
        if (falsepath) {
            // mu=1 in disabled path
            ll1 *= 0;
            if (debug_2) {
                cout << endl << "------------------------------";
                cout << endl << "- ll1(0): " << endl << "  " << ll1;
            }
            for (vi = cs_dis.begin(); vi != cs_dis.end(); ++vi) {
                ll1 *= 0;
                if (debug_2) {
                    cout << endl
                         << "- vi=cs_dis.begin()~end(): " << endl
                         << "  " << (*vi);
                }
                for (i = 0; i <= n; i++)
                    ll1[l1 + i] =
                        handle_integers((*vi).coefficient(Variable(i)));
                if (debug_2) {
                    cout << endl << "  ll1(l1): " << endl << "  " << ll1;
                    if ((*vi).is_inequality()) {
                        cout << " >= 0 ";
                    } else if ((*vi).is_equality()) {
                        cout << " == 0 ";
                    }
                }
                /*
                // l2 is trivial for intra-transition
                for(i=0;i<=n;i++)
                   ll1[l2+i]=handle_integers((*vi).coefficient(Variable(offset1+i)));
                */
                if (debug_2) {
                    cout << endl << "  ll1(l2): " << endl << "  " << ll1;
                    if ((*vi).is_inequality()) {
                        cout << " >= 0 ";
                    } else if ((*vi).is_equality()) {
                        cout << " == 0 ";
                    }
                }
                ll1[nd] = handle_integers((*vi).inhomogeneous_term());
                if (debug_2) {
                    cout << endl << "  ll1(nd): " << endl << "  " << ll1;
                    if ((*vi).is_inequality()) {
                        cout << " >= 0 ";
                    } else if ((*vi).is_equality()) {
                        cout << " == 0 ";
                    }
                }
                if ((*vi).is_inequality())
                    pdis1.add_constraint((ll1.to_lin_expression()) >= 0);
                else if ((*vi).is_equality())
                    pdis1.add_constraint((ll1.to_lin_expression()) == 0);
            }
            preloc_d_cl->insert(pdis1);
            if (debug_2) {
                cout << endl
                     << "- pdis1(mu=1 in disabled path): " << endl
                     << "  " << pdis1;
            }
        }
        cout << endl
             << "  pushing back clump with " << preloc_d_cl->get_count()
             << " Polyhedra (in falsepath)...";
    }

    cout << endl
         << "< < < Intra-Transition::" << name
         << " prepare to push back clump with " << preloc_d_cl->get_count()
         << " Polyhedra";

#ifdef __DEBUG__D_
    cout << "Test Message from "
            "TransitionRelation::compute_constraints(Context &)"
         << endl;
    cout << c;
    cout << "Message ends" << endl << endl;
#endif
}

void TransitionRelation::compute_consecution_01(vector<Clump>& vcl) {
    cout << endl;
    cout << endl
         << "> > > (inter transition) In compute_consecution_01(), "
            "TransitionRelation : "
         << name;
    Clump cl(fd, name, "Transition");
    bool compute_this_trans = true;
    cout << endl << "Current transition has poly as follows: ";
    cout << endl << "  " << *rel;

    // if transition has false-relation, then ignore it
    // (trsat==true) means that opening the verification for transition-sat
    if (trsat) {
        if (rel->is_empty()) {
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
        int nd = fd->get_dimension();
        cs = rel->minimized_constraints();
        int l1 = preloc->get_range_left(), l2 = postloc->get_range_left();
        int i, j;
        C_Polyhedron polyd(2 * n + 2 + nc, UNIVERSE);
        C_Polyhedron polyd_dis(2 * n + 2 + nc, UNIVERSE);
        int offset1 = n + 1, offset2 = 2 * n + 2;
        Linear_Expression ll(0);
        if (debug_3) {
            cout << endl << "------------------------------";
            cout << endl << "- nd: " << nd;
            cout << endl << "- n: " << n;
            cout << endl << "- l1: " << l1;
            cout << endl << "- l2: " << l2;
            cout << endl << "- offset1: " << offset1;
            cout << endl << "- offset2: " << offset2;
        }

        // (1) first the constraints on the unprimed variables
        for (i = 0; i < n; i++) {
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
        for (i = 0; i < n; i++) {
            ll = -1 * Variable(offset1 + i);  // - c_postloc_i
            j = 0;
            for (vi = cs.begin(); vi != cs.end(); vi++) {
                ll += handle_integers((*vi).coefficient(Variable(n + i))) *
                      Variable(offset2 + j);  // coefficient for \lambda_j
                j++;
            }
            // polyd.add_constraint_and_minimize(ll==0);
            polyd.add_constraint(ll == 0);
        }
        for (i = 0; i < n; i++) {
            // disabled path; added by Hongming, at Shanghai Jiao Tong
            // University, 2022/09/13
            ll = Linear_Expression(0);
            j = 0;
            for (vi = cs.begin(); vi != cs.end(); vi++) {
                ll += handle_integers((*vi).coefficient(Variable(n + i))) *
                      Variable(offset2 + j);  // coefficient for \lambda_j
                j++;
            }
            // polyd.add_constraint_and_minimize(ll==0);
            polyd_dis.add_constraint(ll == 0);
        }

        // (3) Constraints on the constant variable
        ll = -Variable(n);  // -M * d_preloc
        j = 0;
        for (vi = cs.begin(); vi != cs.end(); vi++) {
            ll += -handle_integers((*vi).inhomogeneous_term()) *
                  Variable(offset2 + j);  // -coefficient for \lambda_j
            j++;
        }
        polyd_dis.add_constraint(
            ll >= 1);  // disabled path; added by Hongming, at
                       // Shanghai Jiao Tong University, 2022/09/13
        ll += Variable(offset1 + n);  // + d_postloc
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
        // contains_test(polyd, 2*n+2);
        // Timer test_time_for_remove_higher_space_dimensions;
        //  * * *
        //  Old method for eliminate lambda
        polyd.remove_higher_space_dimensions(2 * n + 2);
        polyd_dis.remove_higher_space_dimensions(
            2 * n + 2);  // disabled path; added by Hongming, at Shanghai Jiao
                         // Tong University, 2022/09/13
        // * * *
        // * * *
        // New method for eliminate lambda: Farkas' Lemma 2.5a, Ax<=b
        // eliminate_by_Farkas(polyd, 2*n+2);
        // eliminate_by_Farkas(polyd_dis, 2*n+2);
        // * * *
        // test_time_for_remove_higher_space_dimensions.stop();
        // cout<<endl<<"- The remove_higher_space_dimensions(in inter location)
        // Time Taken is :
        // "<<test_time_for_remove_higher_space_dimensions.compute_time_elapsed()<<endl;
        if (debug_2) {
            cout << endl
                 << "- polyd_dis(projected away \\lambda): " << endl
                 << "  " << polyd_dis;
        }

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
        C_Polyhedron p0(nd, UNIVERSE), p1(nd, UNIVERSE), pdis0(nd, UNIVERSE),
            pdis1(nd, UNIVERSE);
        // Expression e(nd,r,fd,fm);
        LinExpr ll1(nd, fd);
        if (one) {
            // mu=1
            for (vi = cs.begin(); vi != cs.end(); ++vi) {
                for (i = 0; i <= n; i++)
                    ll1[l1 + i] =
                        handle_integers((*vi).coefficient(Variable(i)));
                for (i = 0; i <= n; i++)
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
                for (i = 0; i <= n; i++)
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
            if (debug_2) {
                cout << endl
                     << "- p0(mu=0 in enabled path): " << endl
                     << "  " << p0;
            }
        }
        cout << endl
             << "  pushing back clump with " << cl.get_count()
             << " Polyhedra...";
        if (falsepath) {
            // mu=1 in disabled path
            ll1 *= 0;
            if (debug_2) {
                cout << endl << "------------------------------";
                cout << endl << "- ll1: " << endl << "  " << ll1;
            }
            for (vi = cs_dis.begin(); vi != cs_dis.end(); ++vi) {
                ll1 *= 0;
                if (debug_2) {
                    cout << endl
                         << "- vi=cs_dis.begin()~end(): " << endl
                         << "  " << (*vi);
                }
                for (i = 0; i <= n; i++)
                    ll1[l1 + i] =
                        handle_integers((*vi).coefficient(Variable(i)));
                for (i = 0; i <= n; i++)
                    ll1[l2 + i] = handle_integers(
                        (*vi).coefficient(Variable(offset1 + i)));
                ll1[nd] = handle_integers((*vi).inhomogeneous_term());
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
              for(i=0;i<=n;i++)
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
        vcl.push_back(cl);
    }
    cout << "done";

    return;
}

void TransitionRelation::compute_consecution_constraints(vector<Clump>& vcl,
                                                         C_Polyhedron& initp) {
    // First make up a context and add the initiation constraints to it
    if (preloc->get_name() != postloc->get_name()) {
        compute_consecution_01(vcl);
        return;
    }

    Context* cc = preloc->get_context();
    compute_consecution_constraints(*cc);

    /*
    Constraint_System cs;




    Constraint_System::const_iterator vi;

    int r = fm->get_dimension(); // the number of multiplier variables
    int nd= fd->get_dimension();

    cs=rel->minimized_constraints();

    int l1=preloc->get_range_left(), l2=postloc->get_range_left();

    int i,j;

    C_Polyhedron polyd(2*n+2+nc, UNIVERSE);
    int offset1=n+1, offset2=2*n+2;
    Linear_Expression ll(0);
    // first the constraints on the unprimed variables
    for(i=0;i<n;i++){

       ll=Variable(i); // place holder for \mu * c_i

       j=0;
       for(vi=cs.begin();vi != cs.end(); vi++){
          ll+= handle_integers((*vi).coefficient(Variable(i))) *
    Variable(offset2+j); // coefficient for \lambda_j j++;
       }

       polyd.add_constraint_and_minimize(ll==0);
    }

    // constraints on the primed variable
    for(i=0;i<n;i++){

       ll= -1* Variable(offset1+i); // - c_postloc_i

       j=0;

       for(vi=cs.begin();vi != cs.end(); vi++){
          ll+= handle_integers((*vi).coefficient(Variable(n+i))) *
    Variable(offset2+j); // coefficient for \lambda_j j++;
       }

       polyd.add_constraint_and_minimize(ll==0);
    }

    // Constraints on the constant variable


    ll=-Variable(n); // -M * d_preloc

    j=0;
    for(vi=cs.begin();vi != cs.end(); vi++){
       ll+= - handle_integers((*vi).inhomogeneous_term())*Variable(offset2+j);
    // -coefficient for \lambda_j j++;
    }
    ll+=Variable(offset1+n); // + d_preloc

    polyd.add_constraint_and_minimize(ll>=0) ;

    // Now for the positivity constraint

    j=0;
    for (vi=cs.begin();vi!=cs.end(); ++vi){

       if ((*vi).type()==Constraint::NONSTRICT_INEQUALITY){
          polyd.add_constraint_and_minimize(Variable(offset2+j)>=0);
       } else if ((*vi).type()==Constraint::STRICT_INEQUALITY){
          cerr<<"Location::compute_dual_constraints -- Warning: Encountered
    Strict Inequality"<<endl; cerr<<"                "<<(*vi)<<endl;
          polyd.add_constraint_and_minimize(Variable(offset2+j)>0);

       }

       j++;
    }


    polyd.remove_higher_space_dimensions(2*n+2);
    // now populate the context

       // now populate the context
    cs=polyd.minimized_constraints();

    Expression e(nd,r,fd,fm);

    for (vi=cs.begin();vi !=cs.end();++vi){
       for(i=0;i<=n;i++)
          e[index].set_coefficient( l1+i,
                                    handle_integers((*vi).coefficient(Variable(i)))
                                    );

       for(i=0;i<=n;i++)
          e[r].set_coefficient( l2+i ,
                                handle_integers
    ((*vi).coefficient(Variable(offset1+i)))
                               );

       if ((*vi).is_inequality())
          cc->add_inequality_expression(Expression(e));
       else if ((*vi).is_equality())
          cc->add_equality_expression(Expression(e));

    }

     cc->simplify_repeat();
    */
    // nothing to be done with the clump in this case
    return;
}

void TransitionRelation::populate_multipliers() {
    index = fm->get_dimension();
    string str = "M_" + name;
    fm->insert(str.c_str());
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
    return *rel;
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
    C_Polyhedron post_p(n, UNIVERSE);
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
    temp.add_space_dimensions_and_embed(n);
    rel->intersection_assign(temp);
    compute_nc();
    return;
}

void TransitionRelation::dualize_standard(C_Polyhedron& result) const {
    result = C_Polyhedron(2 * n + 2 + nc, UNIVERSE);
    Constraint_System cs = rel->minimized_constraints();
    Constraint_System::const_iterator vi;
    bool flag = true;
    int i;
    int j, k;

    //
    // dualize & build the constraints
    // \rho \models c_1 x_1 + ... + c_{n+2} x_1' + .. + c_{2n+1} x_n' + c_{n+1}
    // + c_{2n+2} >=0
    //

    for (i = 0; i < n; ++i) {
        Linear_Expression ll;
        ll += -1 * Variable(i);
        flag = true;
        for (k = 0, vi = cs.begin(); vi != cs.end(); ++k, ++vi) {
            flag &= handle_integers((*vi).coefficient(Variable(i)), j);
            ll += j * Variable(2 * n + 2 + k);
        }
        INVARIANT(flag,
                  " Fatal overflow in TransitionRelation::dualize_standard ");

        result.add_constraint(ll == 0);
    }

    for (i = n + 1; i < 2 * n + 1; ++i) {
        Linear_Expression ll;
        ll += -1 * Variable(i);
        flag = true;
        for (k = 0, vi = cs.begin(); vi != cs.end(); ++k, ++vi) {
            flag &= handle_integers((*vi).coefficient(Variable(i - 1)), j);
            ll += j * Variable(2 * n + 2 + k);
        }
        INVARIANT(flag,
                  " Fatal overflow in TransitionRelation::dualize_standard ");

        result.add_constraint(ll == 0);
    }

    // now for the constraint on the constant term
    Linear_Expression ll1;
    ll1 = -1 * Variable(n) - Variable(2 * n + 1);
    flag = true;
    for (k = 0, vi = cs.begin(); vi != cs.end(); ++k, ++vi) {
        flag &= handle_integers((*vi).inhomogeneous_term(), j);
        ll1 += j * Variable(2 * n + 2 + k);
    }
    INVARIANT(flag, " Fatal overflow in TransitionRelation::dualize_standard ");

    result.add_constraint(ll1 <= 0);

    // now add the constraints on the multipliers
    for (k = 0, vi = cs.begin(); vi != cs.end(); ++vi, ++k) {
        if ((*vi).is_equality())
            continue;
        if ((*vi).is_nonstrict_inequality())
            result.add_constraint(Variable(2 * n + 2 + k) >= 0);
        else
            result.add_constraint(Variable(2 * n + 2 + k) > 0);
    }

    // project off the dimension..

    result.remove_higher_space_dimensions(2 * n + 2);
    return;
}

void TransitionRelation::check_map() {
    C_Polyhedron& pre_invariant = preloc->invariant_reference();
    C_Polyhedron& post_invariant = postloc->invariant_reference();

    C_Polyhedron temp(n, UNIVERSE);

    compute_post_new(&pre_invariant, temp);

    if (!post_invariant.contains(temp)) {
        cerr << " consecution failed for transition:" << *this << endl;
    }
    return;
}
