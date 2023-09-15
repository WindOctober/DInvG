
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

#include <assert.h>
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

void TransitionRelation::initialize(int varsNum,
                                    var_info* info,
                                    var_info* dualInfo,
                                    var_info* lambdaInfo,
                                    Location* preloc,
                                    Location* postloc,
                                    C_Polyhedron* rel,
                                    string name) {
    this->varsNum = varsNum;
    this->info = info;
    fp = info->prime();
    this->dualInfo = dualInfo;

    this->lambdaInfo = lambdaInfo;
    this->preloc = preloc;
    this->postloc = postloc;
    this->trans_poly = rel;
    this->name = name;
    populate_multipliers();
    fired = 0;

    guard = new C_Polyhedron(varsNum, UNIVERSE);
    update = new C_Polyhedron(2 * varsNum, UNIVERSE);
}

void TransitionRelation::initialize(int varsNum,
                                    var_info* info,
                                    var_info* dualInfo,
                                    var_info* lambdaInfo,
                                    string name) {
    this->varsNum = varsNum;
    this->info = info;
    fp = info->prime();
    this->dualInfo = dualInfo;

    this->lambdaInfo = lambdaInfo;

    this->name = name;
    populate_multipliers();
    fired = 0;

    guard = new C_Polyhedron(varsNum, UNIVERSE);
    update = new C_Polyhedron(2 * varsNum, UNIVERSE);
}

void TransitionRelation::InitWithoutPopulating(int varsNum,
                                                       var_info* info,
                                                       var_info* dualInfo,
                                                       var_info* lambdaInfo,
                                                       Location* preloc,
                                                       Location* postloc,
                                                       C_Polyhedron* rel,
                                                       string name,
                                                       int index) {
    this->varsNum = varsNum;
    this->info = info;
    fp = info->prime();
    this->dualInfo = dualInfo;

    this->lambdaInfo = lambdaInfo;
    this->preloc = preloc;
    this->postloc = postloc;
    this->trans_poly = rel;
    this->name = name;
    this->index = index;
    fired = 0;

    guard = new C_Polyhedron(varsNum, UNIVERSE);
    update = new C_Polyhedron(2 * varsNum, UNIVERSE);
}

void TransitionRelation::InitWithoutPopulating(int varsNum,
                                                       var_info* info,
                                                       var_info* dualInfo,
                                                       var_info* lambdaInfo,
                                                       string name,
                                                       int index) {
    this->varsNum = varsNum;
    this->info = info;
    fp = info->prime();
    this->dualInfo = dualInfo;

    this->lambdaInfo = lambdaInfo;
    this->index = index;
    this->name = name;
    fired = 0;

    guard = new C_Polyhedron(varsNum, UNIVERSE);
    update = new C_Polyhedron(2 * varsNum, UNIVERSE);
}

// The function checks whether the constraint includes primed variables. If it
// does not include primed variables, it is considered as a guard.
bool TransitionRelation::add_guard(Constraint const& constraint) {
    int res;
    bool flag = true;
    // make sure the coefficients of primed part is zero.
    for (int i = varsNum; i < 2 * varsNum; ++i) {
        flag = handle_integers(constraint.coefficient(Variable(i)), res);
        if (res != 0 || !flag)
            return false;
    }

    flag = handle_integers(constraint.inhomogeneous_term(), res);

    Linear_Expression ll(res);

    for (int i = 0; i < varsNum; ++i) {
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

    for (int i = 0; i < varsNum; ++i) {
        flag &= handle_integers(cc.coefficient(Variable(i)), coef);
        flag &= handle_integers(cc.coefficient(Variable(i + varsNum)),
                                primed_coef);
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
    Constraint_System constraints = trans_poly->minimized_constraints();

    for (auto it = constraints.begin(); it != constraints.end(); ++it) {
        if (add_guard((*it)) || add_preservation_relation((*it)))
            continue;
        update->add_constraint((*it));
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
    // q is a varsNum dimensional polyhedron for which one needs to
    // compute the post operation
    //

    q.intersection_assign((*guard));

    if (q.is_empty())
        return;

    q.add_space_dimensions_and_embed(varsNum);

    // now transform q for each preserved relation
    set<int>::iterator it;

    for (it = preserved.begin(); it != preserved.end(); ++it) {
        Linear_Expression ll = Variable((*it));
        q.affine_image(Variable((*it) + varsNum),
                       ll);  // transforming
                             // each preserved relation
    }

    q.intersection_assign((*update));

    Variables_Set vs;

    int i;
    for (i = 0; i < varsNum; i++) {
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
    compute_constraints_num();
    split_relation();
}

void TransitionRelation::compute_constraints_num() {
    Constraint_System constraints = trans_poly->minimized_constraints();
    Constraint_System::const_iterator it;
    string str;
    constraints_num = 0;

    for (it = constraints.begin(); it != constraints.end(); ++it)
        constraints_num++;
}

TransitionRelation::TransitionRelation(int varsNum,
                                       var_info* info,
                                       var_info* dualInfo,
                                       var_info* lambdaInfo,
                                       string name) {
    initialize(varsNum, info, dualInfo, lambdaInfo, name);
}

TransitionRelation::TransitionRelation(int varsNum,
                                       var_info* info,
                                       var_info* dualInfo,
                                       var_info* lambdaInfo,
                                       Location* preloc,
                                       Location* postloc,
                                       C_Polyhedron* rel,
                                       string name) {
    initialize(varsNum, info, dualInfo, lambdaInfo, preloc, postloc, rel,
               name);
}

TransitionRelation::TransitionRelation(int varsNum,
                                       var_info* info,
                                       var_info* dualInfo,
                                       var_info* lambdaInfo,
                                       string name,
                                       int index) {
    InitWithoutPopulating(varsNum, info, dualInfo, lambdaInfo, name,
                                  index);
}

TransitionRelation::TransitionRelation(int varsNum,
                                       var_info* info,
                                       var_info* dualInfo,
                                       var_info* lambdaInfo,
                                       Location* preloc,
                                       Location* postloc,
                                       C_Polyhedron* rel,
                                       string name,
                                       int index) {
    InitWithoutPopulating(varsNum, info, dualInfo, lambdaInfo,
                                  preloc, postloc, rel, name, index);
}

void TransitionRelation::strengthen(const C_Polyhedron* p) {
    guard->intersection_assign(*p);  // update the guard

    C_Polyhedron* q = new C_Polyhedron(*p);
    q->add_space_dimensions_and_embed(varsNum);
    trans_poly->intersection_assign(*q);
    delete (q);

    compute_constraints_num();
    split_relation();
}

void TransitionRelation::compute_post(const C_Polyhedron* p,
                                      C_Polyhedron& q) const {
    // assume that q=*p
    q = *p;

    q.add_space_dimensions_and_embed(varsNum);

    q.intersection_assign(*trans_poly);

    Variables_Set vs;

    int i;
    for (i = 0; i < varsNum; i++)
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
        int lambda_num = lambdaInfo->get_dimension();
        int dual_num = dualInfo->get_dimension();
        Constraint_System constraints = trans_poly->minimized_constraints();
        Constraint_System cs_dis;
        Constraint_System::const_iterator it;
        int pre_lindex = preloc->get_range_left(),
            post_lindex = postloc->get_range_left();
        int i, j;
        C_Polyhedron enable_poly(2 * varsNum + 2 + constraints_num, UNIVERSE);
        C_Polyhedron disable_poly(2 * varsNum + 2 + constraints_num, UNIVERSE);
        int offset = varsNum + 1, primed_offset = 2 * varsNum + 2;
        Linear_Expression expr(0);
        // (1) first the constraints on the unprimed variables
        for (i = 0; i < varsNum; i++) {
            expr = Variable(i);  //\mu=1 to eliminate the secondary constraint.
            j = 0;
            for (it = constraints.begin(); it != constraints.end(); it++) {
                expr +=
                    handle_integers((*it).coefficient(Variable(i))) *
                    Variable(primed_offset + j);  // coefficient for \lambda_j
                j++;
            }
            enable_poly.add_constraint(expr == 0);
            disable_poly.add_constraint(expr == 0);
        }

        // (2) constraints on the primed variable
        for (i = 0; i < varsNum; i++) {
            expr = -1 * Variable(offset + i);  // - c_postloc_i
            j = 0;
            for (it = constraints.begin(); it != constraints.end(); it++) {
                expr +=
                    handle_integers((*it).coefficient(Variable(varsNum + i))) *
                    Variable(primed_offset + j);
                j++;
            }
            enable_poly.add_constraint(expr == 0);
        }

        for (i = 0; i < varsNum; i++) {
            expr = Linear_Expression(0);
            j = 0;
            for (it = constraints.begin(); it != constraints.end(); it++) {
                expr +=
                    handle_integers((*it).coefficient(Variable(varsNum + i))) *
                    Variable(primed_offset + j);
                j++;
            }
            disable_poly.add_constraint(expr == 0);
        }

        // (3) Constraints on the constant variable
        expr = Variable(varsNum);
        j = 0;
        for (it = constraints.begin(); it != constraints.end(); it++) {
            expr += handle_integers((*it).inhomogeneous_term()) *
                    Variable(primed_offset + j);
            j++;
        }
        disable_poly.add_constraint(expr <= -1);
        expr -= Variable(offset + varsNum);
        enable_poly.add_constraint(expr <= 0);

        // (4) Now for the positivity constraint (or \lambda >= 0 or \forall
        // \lambda)
        j = 0;
        for (it = constraints.begin(); it != constraints.end(); ++it) {
            if ((*it).type() == Constraint::NONSTRICT_INEQUALITY) {
                enable_poly.add_constraint(Variable(primed_offset + j) >= 0);
                disable_poly.add_constraint(Variable(primed_offset + j) >= 0);
            } else if ((*it).type() == Constraint::STRICT_INEQUALITY) {
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

        enable_poly.remove_higher_space_dimensions(2 * varsNum + 2);
        disable_poly.remove_higher_space_dimensions(2 * varsNum + 2);
        // now populate the context
        constraints = enable_poly.minimized_constraints();
        cs_dis = disable_poly.minimized_constraints();

        Expression e(dual_num, lambda_num, dualInfo, lambdaInfo);
        C_Polyhedron pdis1(dual_num, UNIVERSE);
        LinExpr ll1(dual_num, dualInfo);
        for (it = constraints.begin(); it != constraints.end(); ++it) {
            for (i = 0; i <= varsNum; i++)
                e[index].set_coefficient(
                    pre_lindex + i,
                    handle_integers((*it).coefficient(Variable(i))));

            for (i = 0; i <= varsNum; i++)
                e[lambda_num].set_coefficient(
                    post_lindex + i,
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
                for (i = 0; i <= varsNum; i++)
                    ll1[pre_lindex + i] =
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
    Clump clump(dualInfo, name, "Transition");
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
        Constraint_System constraints, cs_dis;
        Constraint_System::const_iterator it;
        int dual_num = dualInfo->get_dimension();
        constraints = trans_poly->minimized_constraints();
        int pre_lindex = preloc->get_range_left(),
            post_lindex = postloc->get_range_left();
        int i, j;
        C_Polyhedron enable_poly(2 * varsNum + 2 + constraints_num, UNIVERSE);
        C_Polyhedron disable_poly(2 * varsNum + 2 + constraints_num, UNIVERSE);
        int offset = varsNum + 1, primed_offset = 2 * varsNum + 2;
        Linear_Expression expr(0);
        // (1) first the constraints on the unprimed variables
        for (i = 0; i < varsNum; i++) {
            expr = Variable(i);  // place holder for \mu * c_i
            j = 0;
            for (it = constraints.begin(); it != constraints.end(); it++) {
                expr +=
                    handle_integers((*it).coefficient(Variable(i))) *
                    Variable(primed_offset + j);  // coefficient for \lambda_j
                j++;
            }
            enable_poly.add_constraint(expr == 0);
            disable_poly.add_constraint(expr == 0);
        }

        // (2) constraints on the primed variable
        for (i = 0; i < varsNum; i++) {
            expr = -1 * Variable(offset + i);  // - c_postloc_i
            j = 0;
            for (it = constraints.begin(); it != constraints.end(); it++) {
                expr +=
                    handle_integers((*it).coefficient(Variable(varsNum + i))) *
                    Variable(primed_offset + j);
                j++;
            }
            enable_poly.add_constraint(expr == 0);
        }
        for (i = 0; i < varsNum; i++) {
            expr = Linear_Expression(0);
            j = 0;
            for (it = constraints.begin(); it != constraints.end(); it++) {
                expr +=
                    handle_integers((*it).coefficient(Variable(varsNum + i))) *
                    Variable(primed_offset + j);  // coefficient for \lambda_j
                j++;
            }
            disable_poly.add_constraint(expr == 0);
        }

        // (3) Constraints on the constant variable
        expr = Variable(varsNum);
        j = 0;
        for (it = constraints.begin(); it != constraints.end(); it++) {
            expr += handle_integers((*it).inhomogeneous_term()) *
                    Variable(primed_offset + j);
            j++;
        }
        disable_poly.add_constraint(expr <= -1);
        expr -= Variable(offset + varsNum);
        enable_poly.add_constraint(expr <= 0);

        // (4) Now for the positivity constraint (or \lambda >= 0 or \forall
        // \lambda)
        j = 0;
        for (it = constraints.begin(); it != constraints.end(); ++it) {
            if ((*it).type() == Constraint::NONSTRICT_INEQUALITY) {
                enable_poly.add_constraint(Variable(primed_offset + j) >= 0);
                disable_poly.add_constraint(Variable(primed_offset + j) >= 0);
            } else if ((*it).type() == Constraint::STRICT_INEQUALITY) {
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

        enable_poly.remove_higher_space_dimensions(2 * varsNum + 2);
        disable_poly.remove_higher_space_dimensions(2 * varsNum + 2);

        // now create two input polyhedra
        constraints = enable_poly.minimized_constraints();
        cs_dis = disable_poly.minimized_constraints();
        LinExpr template_expr(dual_num, dualInfo);
        if (one) {
            C_Polyhedron polyhedron(dual_num, UNIVERSE);
            for (it = constraints.begin(); it != constraints.end(); ++it) {
                for (i = 0; i <= varsNum; i++) {
                    template_expr[pre_lindex + i] =
                        handle_integers((*it).coefficient(Variable(i)));
                    template_expr[post_lindex + i] = handle_integers(
                        (*it).coefficient(Variable(offset + i)));
                }
                if ((*it).is_inequality())
                    polyhedron.add_constraint(
                        (template_expr.to_lin_expression()) >= 0);
                else if ((*it).is_equality())
                    polyhedron.add_constraint(
                        (template_expr.to_lin_expression()) == 0);
            }
            clump.insert(polyhedron);
        }
        cout << endl
             << "  pushing back clump with " << clump.get_count()
             << " Polyhedra...";
        if (zero) {
            C_Polyhedron polyhedron(dual_num, UNIVERSE);
            template_expr *= 0;
            for (it = constraints.begin(); it != constraints.end(); ++it) {
                for (i = 0; i <= varsNum; i++)
                    template_expr[post_lindex + i] = handle_integers(
                        (*it).coefficient(Variable(offset + i)));
                if ((*it).is_inequality())
                    polyhedron.add_constraint(
                        (template_expr.to_lin_expression()) >= 0);
                else if ((*it).is_equality())
                    polyhedron.add_constraint(
                        (template_expr.to_lin_expression()) == 0);
            }
            clump.insert(polyhedron);
        }
        cout << endl
             << "  pushing back clump with " << clump.get_count()
             << " Polyhedra...";
        if (falsepath) {
            C_Polyhedron polyhedron(dual_num, UNIVERSE);
            // mu=1 in disabled path
            template_expr *= 0;
            for (it = cs_dis.begin(); it != cs_dis.end(); ++it) {
                template_expr *= 0;
                for (i = 0; i <= varsNum; i++){
                    template_expr[pre_lindex + i] =
                        handle_integers((*it).coefficient(Variable(i)));
                    template_expr[post_lindex + i] = handle_integers(
                        (*it).coefficient(Variable(offset + i)));
                }
                template_expr[dual_num] =
                    handle_integers((*it).inhomogeneous_term());
                if ((*it).is_inequality())
                    polyhedron.add_constraint(
                        (template_expr.to_lin_expression()) >= 0);
                else if ((*it).is_equality())
                    polyhedron.add_constraint(
                        (template_expr.to_lin_expression()) == 0);
            }
            clump.insert(polyhedron);
        }
        cout << endl
             << "  pushing back clump with " << clump.get_count()
             << " Polyhedra (in falsepath)...";
    }
    cout << endl
         << "< < < Inter-Transition::" << name << " pushing back clump with "
         << clump.get_count() << " Polyhedra...";
    if (clump.get_count() != 0) {
        clumps.push_back(clump);
    }
    cout << "done";

    return;
}

void TransitionRelation::compute_consecution_constraints(vector<Clump>& vcl) {
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
    index = lambdaInfo->get_dimension();
    string str = "M_" + name;
    lambdaInfo->insert(str.c_str());
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
    C_Polyhedron post_p(varsNum, UNIVERSE);
    compute_post_new(pre_p, post_p);

    postloc->setPoly(&post_p);

    fired++;
    return true;
}

int TransitionRelation::get_firing_count() {
    return fired;
}

void TransitionRelation::add_preloc_invariant() {
    C_Polyhedron temp(preloc->inv_poly_reference());
    guard->intersection_assign(temp);
    temp.add_space_dimensions_and_embed(varsNum);
    trans_poly->intersection_assign(temp);
    compute_constraints_num();
    return;
}

void TransitionRelation::check_map() {
    C_Polyhedron& pre_invariant = preloc->invariant_reference();
    C_Polyhedron& post_invariant = postloc->invariant_reference();

    C_Polyhedron temp(varsNum, UNIVERSE);

    compute_post_new(&pre_invariant, temp);

    if (!post_invariant.contains(temp)) {
        cerr << " consecution failed for transition:" << *this << endl;
    }
    return;
}
