
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


void TransitionRelation::initialize(int varsNum,
                                    var_info* info,
                                    var_info* coefInfo,
                                    var_info* lambdaInfo,
                                    Location* preLoc,
                                    Location* postLoc,
                                    C_Polyhedron* rel,
                                    string name) {
    this->varsNum = varsNum;
    this->info = info;
    fp = info->prime();
    this->coefInfo = coefInfo;

    this->lambdaInfo = lambdaInfo;
    this->preLoc = preLoc;
    this->postLoc = postLoc;
    this->transPoly = rel;
    this->name = name;
    populate_multipliers();

    guard = new C_Polyhedron(varsNum, UNIVERSE);
    update = new C_Polyhedron(2 * varsNum, UNIVERSE);
}

void TransitionRelation::initialize(int varsNum,
                                    var_info* info,
                                    var_info* coefInfo,
                                    var_info* lambdaInfo,
                                    string name) {
    this->varsNum = varsNum;
    this->info = info;
    fp = info->prime();
    this->coefInfo = coefInfo;

    this->lambdaInfo = lambdaInfo;

    this->name = name;
    populate_multipliers();

    guard = new C_Polyhedron(varsNum, UNIVERSE);
    update = new C_Polyhedron(2 * varsNum, UNIVERSE);
}

void TransitionRelation::InitWithoutPopulating(int varsNum,
                                               var_info* info,
                                               var_info* coefInfo,
                                               var_info* lambdaInfo,
                                               Location* preLoc,
                                               Location* postLoc,
                                               C_Polyhedron* rel,
                                               string name,
                                               int index) {
    this->varsNum = varsNum;
    this->info = info;
    fp = info->prime();
    this->coefInfo = coefInfo;

    this->lambdaInfo = lambdaInfo;
    this->preLoc = preLoc;
    this->postLoc = postLoc;
    this->transPoly = rel;
    this->name = name;
    this->index = index;

    guard = new C_Polyhedron(varsNum, UNIVERSE);
    update = new C_Polyhedron(2 * varsNum, UNIVERSE);
}

void TransitionRelation::InitWithoutPopulating(int varsNum,
                                               var_info* info,
                                               var_info* coefInfo,
                                               var_info* lambdaInfo,
                                               string name,
                                               int index) {
    this->varsNum = varsNum;
    this->info = info;
    fp = info->prime();
    this->coefInfo = coefInfo;

    this->lambdaInfo = lambdaInfo;
    this->index = index;
    this->name = name;

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
        flag = handleInt(constraint.coefficient(Variable(i)), res);
        if (res != 0 || !flag)
            return false;
    }

    flag = handleInt(constraint.inhomogeneous_term(), res);

    Linear_Expression ll(res);

    for (int i = 0; i < varsNum; ++i) {
        flag &= handleInt(constraint.coefficient(Variable(i)), res);
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
    flag = handleInt(cc.inhomogeneous_term(), coef);

    if (!flag || coef != 0)
        return false;

    for (int i = 0; i < varsNum; ++i) {
        flag &= handleInt(cc.coefficient(Variable(i)), coef);
        flag &= handleInt(cc.coefficient(Variable(i + varsNum)), primed_coef);
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
    Constraint_System constraints = transPoly->minimized_constraints();

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

void TransitionRelation::setLocs(Location* preLoc, Location* postLoc) {
    this->preLoc = preLoc;
    this->postLoc = postLoc;
}
void TransitionRelation::setRel(C_Polyhedron* rel) {
    this->transPoly = rel;
    ResetConstraintsNum();
    split_relation();
}

void TransitionRelation::ResetConstraintsNum() {
    Constraint_System constraints = transPoly->minimized_constraints();
    Constraint_System::const_iterator it;
    string str;
    constraints_num = 0;

    for (it = constraints.begin(); it != constraints.end(); ++it)
        constraints_num++;
}

TransitionRelation::TransitionRelation(int varsNum,
                                       var_info* info,
                                       var_info* coefInfo,
                                       var_info* lambdaInfo,
                                       string name) {
    initialize(varsNum, info, coefInfo, lambdaInfo, name);
}

TransitionRelation::TransitionRelation(int varsNum,
                                       var_info* info,
                                       var_info* coefInfo,
                                       var_info* lambdaInfo,
                                       Location* preLoc,
                                       Location* postLoc,
                                       C_Polyhedron* rel,
                                       string name) {
    initialize(varsNum, info, coefInfo, lambdaInfo, preLoc, postLoc, rel, name);
}

TransitionRelation::TransitionRelation(int varsNum,
                                       var_info* info,
                                       var_info* coefInfo,
                                       var_info* lambdaInfo,
                                       string name,
                                       int index) {
    InitWithoutPopulating(varsNum, info, coefInfo, lambdaInfo, name, index);
}

TransitionRelation::TransitionRelation(int varsNum,
                                       var_info* info,
                                       var_info* coefInfo,
                                       var_info* lambdaInfo,
                                       Location* preLoc,
                                       Location* postLoc,
                                       C_Polyhedron* rel,
                                       string name,
                                       int index) {
    InitWithoutPopulating(varsNum, info, coefInfo, lambdaInfo, preLoc, postLoc,
                          rel, name, index);
}

void TransitionRelation::strengthen(const C_Polyhedron* p) {
    guard->intersection_assign(*p);  // update the guard

    C_Polyhedron* q = new C_Polyhedron(*p);
    q->add_space_dimensions_and_embed(varsNum);
    transPoly->intersection_assign(*q);
    delete (q);

    ResetConstraintsNum();
    split_relation();
}

void TransitionRelation::compute_post(const C_Polyhedron* p,
                                      C_Polyhedron& q) const {
    // assume that q=*p
    q = *p;

    q.add_space_dimensions_and_embed(varsNum);

    q.intersection_assign(*transPoly);

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

void TransitionRelation::ComputeIntraConsecConstraints(Context& context) {
    // Use two expression stores. One for the equations and
    // the other for the inequations
    cout << endl;
    cout << endl
         << "> > > (intra transition) In ComputeIntraConsecConstraints(), "
            "TransitionRelation : "
         << name;
    Clump* disableClump = preLoc->getDisClump();
    bool legalFlag = true;

    if (transPoly->is_empty()) {
        legalFlag = false;
    }
    cout << endl << "  Compute this transition: " << legalFlag;

    if (legalFlag) {
        int lambdaNum = lambdaInfo->getDim();
        int coefNum = coefInfo->getDim();
        Constraint_System constraints = transPoly->minimized_constraints();
        Constraint_System disableCS;
        Constraint_System::const_iterator it;
        int preLIndex = preLoc->getLIndex(), postLIndex = postLoc->getLIndex();
        assert(preLIndex == postLIndex);
        int i, j;
        C_Polyhedron enablePoly(2 * varsNum + 2 + constraints_num, UNIVERSE);
        C_Polyhedron disablePoly(2 * varsNum + 2 + constraints_num, UNIVERSE);
        int postLStart = varsNum + 1, lambdaLStart = 2 * varsNum + 2;
        Linear_Expression expr(0);
        // (1) first the constraints on the unprimed variables
        for (i = 0; i < varsNum; i++) {
            expr = Variable(i);  //\mu=1 to eliminate the secondary constraint.
            j = 0;
            for (it = constraints.begin(); it != constraints.end(); it++) {
                expr += handleInt((*it).coefficient(Variable(i))) *
                        Variable(lambdaLStart + j);
                j++;
            }
            enablePoly.add_constraint(expr == 0);
            disablePoly.add_constraint(expr == 0);
        }

        // (2) constraints on the primed variable
        for (i = 0; i < varsNum; i++) {
            expr = -1 * Variable(postLStart + i);  // - c_postloc_i
            j = 0;
            for (it = constraints.begin(); it != constraints.end(); it++) {
                expr += handleInt((*it).coefficient(Variable(varsNum + i))) *
                        Variable(lambdaLStart + j);
                j++;
            }
            enablePoly.add_constraint(expr == 0);
        }

        for (i = 0; i < varsNum; i++) {
            expr = Linear_Expression(0);
            j = 0;
            for (it = constraints.begin(); it != constraints.end(); it++) {
                expr += handleInt((*it).coefficient(Variable(varsNum + i))) *
                        Variable(lambdaLStart + j);
                j++;
            }
            disablePoly.add_constraint(expr == 0);
        }

        // (3) Constraints on the constant variable
        expr = Variable(varsNum);
        j = 0;
        for (it = constraints.begin(); it != constraints.end(); it++) {
            expr += handleInt((*it).inhomogeneous_term()) *
                    Variable(lambdaLStart + j);
            j++;
        }
        disablePoly.add_constraint(expr <= -1);
        expr -= Variable(postLStart + varsNum);
        enablePoly.add_constraint(expr <= 0);

        // (4) Now for the positivity constraint (or \lambda >= 0 or \forall
        // \lambda)
        j = 0;
        for (it = constraints.begin(); it != constraints.end(); ++it) {
            if ((*it).type() == Constraint::NONSTRICT_INEQUALITY) {
                enablePoly.add_constraint(Variable(lambdaLStart + j) >= 0);
                disablePoly.add_constraint(Variable(lambdaLStart + j) >= 0);
            } else if ((*it).type() == Constraint::STRICT_INEQUALITY) {
                cerr << "Location::ComputeCoefConstraints -- Warning: "
                        "Encountered "
                        "Strict Inequality"
                     << endl;
                cerr << "                " << (*it) << endl;
                enablePoly.add_constraint(Variable(lambdaLStart + j) > 0);
                disablePoly.add_constraint(Variable(lambdaLStart + j) > 0);
            }
            j++;
        }

        enablePoly.remove_higher_space_dimensions(2 * varsNum + 2);
        disablePoly.remove_higher_space_dimensions(2 * varsNum + 2);
        // now populate the context
        constraints = enablePoly.minimized_constraints();
        disableCS = disablePoly.minimized_constraints();

        Expression e(coefNum, lambdaNum, coefInfo, lambdaInfo);
        C_Polyhedron dispoly(coefNum, UNIVERSE);
        LinExpr lexpr(coefNum, coefInfo);
        for (it = constraints.begin(); it != constraints.end(); ++it) {
            for (i = 0; i <= varsNum; i++)
                e[index].setCoefficient(
                    preLIndex + i, handleInt((*it).coefficient(Variable(i))));

            for (i = 0; i <= varsNum; i++)
                e[lambdaNum].setCoefficient(
                    postLIndex + i,
                    handleInt((*it).coefficient(Variable(postLStart + i))));

            if ((*it).is_inequality())
                context.addIneqExpr(Expression(e));
            else if ((*it).is_equality())
                context.addEqExpr(Expression(e));
        }
        // This section corresponds to the false scenario, namely the -1>=0 case
        // in the Farkas Lemma.
        lexpr *= 0;
        for (it = disableCS.begin(); it != disableCS.end(); ++it) {
            lexpr *= 0;
            for (i = 0; i <= varsNum; i++)
                lexpr[preLIndex + i] =
                    handleInt((*it).coefficient(Variable(i)));
            lexpr[coefNum] = handleInt((*it).inhomogeneous_term());
            if ((*it).is_inequality())
                dispoly.add_constraint((lexpr.toLinExpression()) >= 0);
            else if ((*it).is_equality())
                dispoly.add_constraint((lexpr.toLinExpression()) == 0);
        }
        disableClump->insert(dispoly);

        cout << endl
             << "  pushing back clump with " << disableClump->getCount()
             << " Polyhedra (in falsepath)...";
    }

    cout << endl
         << "< < < Intra-Transition::" << name
         << " prepare to push back clump with " << disableClump->getCount()
         << " Polyhedra";
}

void TransitionRelation::ComputeInterConsecConstraints(vector<Clump>& clumps) {
    cout << endl;
    cout << endl
         << "> > > (inter transition) In ComputeInterConsecConstraints(), "
            "TransitionRelation : "
         << name;
    Clump clump(coefInfo, name, "Transition");
    bool transFlag = true;
    if (transPoly->is_empty()) {
        transFlag = false;
    }
    cout << endl << "  Compute this transition: " << transFlag;

    if (transFlag) {
        Constraint_System constraints, disableCS;
        Constraint_System::const_iterator it;
        int coefNum = coefInfo->getDim();
        constraints = transPoly->minimized_constraints();
        int preLIndex = preLoc->getLIndex(), postLIndex = postLoc->getLIndex();
        int i, j;
        C_Polyhedron enablePoly(2 * varsNum + 2 + constraints_num, UNIVERSE);
        C_Polyhedron disablePoly(2 * varsNum + 2 + constraints_num, UNIVERSE);
        int primedIndex = varsNum + 1, lambdaIndex = 2 * varsNum + 2;
        Linear_Expression expr(0);
        // (1) first the constraints on the unprimed variables
        for (i = 0; i < varsNum; i++) {
            expr = Variable(i);  // place holder for \mu * c_i
            j = 0;
            for (it = constraints.begin(); it != constraints.end(); it++) {
                expr += handleInt((*it).coefficient(Variable(i))) *
                        Variable(lambdaIndex + j);  // coefficient for \lambda_j
                j++;
            }
            enablePoly.add_constraint(expr == 0);
            disablePoly.add_constraint(expr == 0);
        }

        // (2) constraints on the primed variable
        for (i = 0; i < varsNum; i++) {
            expr = -1 * Variable(primedIndex + i);  // - c_postloc_i
            j = 0;
            for (it = constraints.begin(); it != constraints.end(); it++) {
                expr += handleInt((*it).coefficient(Variable(varsNum + i))) *
                        Variable(lambdaIndex + j);
                j++;
            }
            enablePoly.add_constraint(expr == 0);
        }
        for (i = 0; i < varsNum; i++) {
            expr = Linear_Expression(0);
            j = 0;
            for (it = constraints.begin(); it != constraints.end(); it++) {
                expr += handleInt((*it).coefficient(Variable(varsNum + i))) *
                        Variable(lambdaIndex + j);  // coefficient for \lambda_j
                j++;
            }
            disablePoly.add_constraint(expr == 0);
        }

        // (3) Constraints on the constant variable
        expr = Variable(varsNum);
        j = 0;
        for (it = constraints.begin(); it != constraints.end(); it++) {
            expr += handleInt((*it).inhomogeneous_term()) *
                    Variable(lambdaIndex + j);
            j++;
        }
        disablePoly.add_constraint(expr <= -1);
        expr -= Variable(primedIndex + varsNum);
        enablePoly.add_constraint(expr <= 0);

        // (4) Now for the positivity constraint (or \lambda >= 0 or \forall
        // \lambda)
        j = 0;
        for (it = constraints.begin(); it != constraints.end(); ++it) {
            if ((*it).type() == Constraint::NONSTRICT_INEQUALITY) {
                enablePoly.add_constraint(Variable(lambdaIndex + j) >= 0);
                disablePoly.add_constraint(Variable(lambdaIndex + j) >= 0);
            } else if ((*it).type() == Constraint::STRICT_INEQUALITY) {
                cerr << "Location::ComputeCoefConstraints -- Warning: "
                        "Encountered "
                        "Strict Inequality"
                     << endl;
                cerr << "                " << (*it) << endl;
                enablePoly.add_constraint(Variable(lambdaIndex + j) > 0);
                disablePoly.add_constraint(Variable(lambdaIndex + j) > 0);
            }
            j++;
        }

        enablePoly.remove_higher_space_dimensions(2 * varsNum + 2);
        disablePoly.remove_higher_space_dimensions(2 * varsNum + 2);

        // now create two input polyhedra
        constraints = enablePoly.minimized_constraints();
        disableCS = disablePoly.minimized_constraints();
        LinExpr templateExpr(coefNum, coefInfo);
        // This section corresponds to the case when \mu=1 in terms of
        // increments. For details, please refer to the optimization in the
        // SAS04 paper.
        C_Polyhedron IncreasingPoly(coefNum, UNIVERSE);
        for (it = constraints.begin(); it != constraints.end(); ++it) {
            for (i = 0; i <= varsNum; i++) {
                templateExpr[preLIndex + i] =
                    handleInt((*it).coefficient(Variable(i)));
                templateExpr[postLIndex + i] =
                    handleInt((*it).coefficient(Variable(primedIndex + i)));
            }
            if ((*it).is_inequality())
                IncreasingPoly.add_constraint((templateExpr.toLinExpression()) >=
                                          0);
            else if ((*it).is_equality())
                IncreasingPoly.add_constraint((templateExpr.toLinExpression()) ==
                                          0);
        }
        clump.insert(IncreasingPoly);
        // This section corresponds to the local case when \mu=0. For details,
        // please refer to the optimization in the SAS04 paper.
        C_Polyhedron LocalPoly(coefNum, UNIVERSE);
        templateExpr *= 0;
        for (it = constraints.begin(); it != constraints.end(); ++it) {
            for (i = 0; i <= varsNum; i++)
                templateExpr[postLIndex + i] =
                    handleInt((*it).coefficient(Variable(primedIndex + i)));
            if ((*it).is_inequality())
                LocalPoly.add_constraint((templateExpr.toLinExpression()) >=
                                          0);
            else if ((*it).is_equality())
                LocalPoly.add_constraint((templateExpr.toLinExpression()) ==
                                          0);
        }
        clump.insert(LocalPoly);
        // This section corresponds to the false scenario, namely the -1>=0 case
        // in the Farkas Lemma.
        C_Polyhedron FalsePoly(coefNum, UNIVERSE);
        templateExpr *= 0;
        for (it = disableCS.begin(); it != disableCS.end(); ++it) {
            templateExpr *= 0;
            for (i = 0; i <= varsNum; i++) {
                templateExpr[preLIndex + i] =
                    handleInt((*it).coefficient(Variable(i)));
                templateExpr[postLIndex + i] =
                    handleInt((*it).coefficient(Variable(primedIndex + i)));
            }
            templateExpr[coefNum] = handleInt((*it).inhomogeneous_term());
            if ((*it).is_inequality())
                FalsePoly.add_constraint((templateExpr.toLinExpression()) >=
                                          0);
            else if ((*it).is_equality())
                FalsePoly.add_constraint((templateExpr.toLinExpression()) ==
                                          0);
        }
        clump.insert(FalsePoly);
    }
    cout << endl
         << "< < < Inter-Transition::" << name << " pushing back clump with "
         << clump.getCount() << " Polyhedra...";
    if (clump.getCount() != 0) {
        clumps.push_back(clump);
    }
    cout << "done";

    return;
}

void TransitionRelation::ComputeIntraConsecConstraints(vector<Clump>& clumps) {
    // First make up a context and add the initiation constraints to it
    if (preLoc->getName() != postLoc->getName()) {
        ComputeInterConsecConstraints(clumps);
        return;
    } else {
        Context* context = preLoc->getContext();
        ComputeIntraConsecConstraints(*context);
    }
    return;
}

void TransitionRelation::populate_multipliers() {
    index = lambdaInfo->getDim();
    string str = "M_" + name;
    lambdaInfo->insert(str.c_str());
}

const string& TransitionRelation::getName() const {
    return name;
}

const string& TransitionRelation::getPreLocName() const {
    return preLoc->getName();
}

const string& TransitionRelation::getPostLocName() const {
    return postLoc->getName();
}

const C_Polyhedron& TransitionRelation::getTransRel() const {
    return *transPoly;
}

C_Polyhedron* TransitionRelation::getTransRelRef() const {
    return transPoly;
}

const var_info* TransitionRelation::getInfo() const {
    return fp;
}

ostream& operator<<(ostream& in, TransitionRelation const& t) {
    // Just print the transition relation
    var_info const* ff = t.getInfo();

    in << "Transition Relation: " << t.getName() << endl;
    in << "Pre-Location:" << t.getPreLocName() << "  "
       << " Post-Location:" << t.getPostLocName() << endl;
    in << "Transition Relation: [[" << endl;
    in << "| " << endl;
    printPolyhedron(in, t.getTransRel(), ff);
    in << "| " << endl;
    in << "]]" << endl;
    in << "Guard: [[" << endl;
    in << "| " << endl;
    printPolyhedron(in, t.get_guard_poly(), ff);
    in << "| " << endl;
    in << "]]" << endl;
    in << "Update: [[" << endl;
    in << "| " << endl;
    printPolyhedron(in, t.get_update_poly(), ff);
    in << "| " << endl;
    in << "]]" << endl;
    in << "Preserved: [[" << endl;
    in << "| " << endl;
    set<int> const& st = t.get_preserved_set();
    set<int>::iterator vxx;
    for (vxx = st.begin(); vxx != st.end(); ++vxx) {
        in << "├ ";
        in << " " << ff->getName((*vxx)) << endl;
    }
    in << "| " << endl;
    in << "]]" << endl;
    in << endl;
    in << "- Transition Relation " << t.getName() << " Ends" << endl;
    in << "----------------------------- " << endl;
    return in;
}

bool TransitionRelation::matches(string& nam) const {
    return (name == nam);
}

void TransitionRelation::addPreInv() {
    C_Polyhedron temp(preLoc->getPreInvRef());
    guard->intersection_assign(temp);
    temp.add_space_dimensions_and_embed(varsNum);
    cout << temp << endl;
    cout << "note" << endl;
    transPoly->intersection_assign(temp);
    ResetConstraintsNum();
    return;
}

void TransitionRelation::check_map() {
    C_Polyhedron& preInv = preLoc->getInvRef();
    C_Polyhedron& postInv = postLoc->getInvRef();

    C_Polyhedron temp(varsNum, UNIVERSE);

    compute_post_new(&preInv, temp);

    if (!postInv.contains(temp)) {
        cerr << " consecution failed for transition:" << *this << endl;
    }
    return;
}
