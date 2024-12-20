
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

#include "Location.h"

#include "Context.h"
#include "Elimination.h"
#include "Macro.h"
#include "PolyUtils.h"
#include "funcs.h"

extern string projection;

void Location::initialize(int varsNum,
                          var_info* info,
                          var_info* coefInfo,
                          var_info* lambdaInfo,
                          C_Polyhedron* p,
                          string name) {
    this->varsNum = varsNum;
    this->info = info;
    this->coefInfo = coefInfo;
    this->lambdaInfo = lambdaInfo;
    this->poly = p;
    this->locName = name;
    this->preInv = new C_Polyhedron(varsNum, UNIVERSE);
    this->disableClump = new Clump(coefInfo, name, "Location");
    setCoefInfo();
    invariant = new C_Polyhedron(varsNum, UNIVERSE);
    contextReady = false;
}

void Location::InitWithoutPopulating(int varsNum,
                                     var_info* info,
                                     var_info* coefInfo,
                                     var_info* lambdaInfo,
                                     C_Polyhedron* p,
                                     string name,
                                     int LIndex) {
    this->varsNum = varsNum;
    this->info = info;
    this->coefInfo = coefInfo;
    this->lambdaInfo = lambdaInfo;
    this->poly = p;
    this->locName = name;
    this->preInv = new C_Polyhedron(varsNum, UNIVERSE);
    this->disableClump = new Clump(coefInfo, name, "Location");
    LIndex = LIndex;
    invariant = new C_Polyhedron(varsNum, UNIVERSE);
    contextReady = false;
}

Context* Location::getContext() {
    return context;
}

void Location::makeContext() {
    context = new Context(info, coefInfo, lambdaInfo);
    contextReady = true;
}

Location::Location(int varsNum,
                   var_info* info,
                   var_info* coefInfo,
                   var_info* lambdaInfo,
                   string name) {
    C_Polyhedron* init = new C_Polyhedron(varsNum, UNIVERSE);
    initialize(varsNum, info, coefInfo, lambdaInfo, init, name);
    initFlag = false;
}

Location::Location(int varsNum,
                   var_info* info,
                   var_info* coefInfo,
                   var_info* lambdaInfo,
                   string name,
                   int LIndex) {
    C_Polyhedron* init = new C_Polyhedron(varsNum, UNIVERSE);
    InitWithoutPopulating(varsNum, info, coefInfo, lambdaInfo, init, name,
                          LIndex);
    initFlag = false;
}

void Location::setPoly(C_Polyhedron* q) {
    if (!initFlag) {
        poly->intersection_assign(*q);
        initFlag = true;
    } else {
        poly->poly_hull_assign(*q);
    }
}

void Location::setInitPoly(C_Polyhedron& q) {
    if (!initFlag) {
        poly->intersection_assign(q);
        initFlag = true;
    } else {
        poly->poly_hull_assign(q);
    }
}

C_Polyhedron* Location::get_initial() {
    return poly;
}

bool Location::isInitLoc() {
    return initFlag;
}

int Location::getDim() const {
    return varsNum;
}

const var_info* Location::getInfo() const {
    return info;
}
const var_info* Location::getCoefInfo() const {
    return coefInfo;
}
int Location::getLIndex() const {
    return LIndex;
}

void Location::addClump(vector<Clump>& clumps) {
    // *** new-empty without disabled-path
    // Clump disClump(coefInfo, name, "Location");
    // ***
    // *** with disabled-path
    Clump disClump = getDisClumpRef();
    // ***
    // cout << endl
    //      << "> > > Location::" << locName << " already has clump with "
    //      << disClump.getCount() << " Polyhedra...";
    context->RecursiveSplit(disClump);
    // cout << endl
    //      << "> > > Location::" << locName
    //      << " altogether pushing back clump with " << disClump.getCount()
    //      << " Polyhedra...";

    clumps.push_back(disClump);
    // cout << "done";
}

bool Location::matches(string name) const {
    return (locName == name);
}

void Location::setCoefInfo() {
    LIndex = coefInfo->getDim();
    string dual_variable;
    for (int i = 0; i < varsNum; i++) {
        dual_variable = "c_" + locName + "_" + int_to_str(i);
        coefInfo->insert(dual_variable.c_str());
    }
    dual_variable = "d_" + locName;
    coefInfo->insert(dual_variable.c_str());
}

string const& Location::getName() const {
    return locName;
}

ostream& operator<<(ostream& in, Location const& l) {
    // details of the location should go in here
    int varsNum = l.getDim();

    const var_info* info = l.getInfo();
    string name = l.getName();
    // The rest to be completed later
    in << endl;
    in << "Location: " << name << endl;
    in << "# of variables: " << varsNum << endl;
    in << "「 l: " << l.getLIndex() << ", varsNum: " << varsNum
       << ", coefNum: " << l.getCoefInfo()->getDim() << " 」" << endl;

    if (l.getInitFlag()) {
        in << "Initial Condition: [[ " << endl;
        in << "| " << endl;
        printPolyhedron(in, l.getPolyRef(), info);
        in << "| " << endl;
        in << "]]" << endl;
    } else {
        in << "[ no initial condition set]" << endl;
    }

    in << "Invariant: [[ " << endl;
    in << "| " << endl;
    printPolyhedron(in, l.GetInv(), info);
    in << "| " << endl;
    in << "]]" << endl;

    return in;
}

void Location::ComputeCoefConstraints() {
    ComputeCoefConstraints(*context);
}
void Location::ComputeCoefConstraints(Context& cc) {
    // Inefficient solution for the time being
    // Just build a polyhedron with the right coefficient variables
    //   and adding dimensions for the multipliers
    // Later expunge the multipliers
    // use >= as the default constraint state.
    // First obtain the number of constraints
    if (!initFlag)
        return;
    Constraint_System constraints = poly->minimized_constraints();
    Constraint_System::const_iterator it;

    C_Polyhedron* result;

    int i, j, constraintNum, coefNum;

    // count the number of multiplier variables required
    constraintNum = 0;
    for (it = constraints.begin(); it != constraints.end(); ++it)
        constraintNum++;

    coefNum = coefInfo->getDim();

    result = new C_Polyhedron(coefNum + constraintNum,
                              UNIVERSE);  // create a universe polyhedron of
                                          // coefNum +constraintNum dimensions
    Linear_Expression lin(0);

    // Now build the constraints
    for (i = 0; i < varsNum; i++) {
        lin = Linear_Expression(0);
        lin = lin - Variable(LIndex + i);  // add -c_i to the constraint
        j = 0;
        for (it = constraints.begin(); it != constraints.end(); ++it) {
            lin = lin + (*it).coefficient(Variable(i)) * Variable(coefNum + j);
            j++;
        }
        result->add_constraint(lin ==
                               0);  // Add the constraint lin==0 to the result
    }

    // Now the constraints on the constant
    lin = Linear_Expression(0);
    lin = lin - Variable(LIndex + varsNum);  // add -d to the constraint
    j = 0;
    for (it = constraints.begin(); it != constraints.end(); ++it) {
        lin = lin + (*it).inhomogeneous_term() * Variable(coefNum + j);
        j++;
    }

    result->add_constraint(lin <= 0);

    // Now the constraints on the multipliers

    j = 0;
    for (it = constraints.begin(); it != constraints.end(); ++it) {
        if ((*it).type() == Constraint::NONSTRICT_INEQUALITY) {
            result->add_constraint(Variable(coefNum + j) >= 0);
        } else if ((*it).type() == Constraint::STRICT_INEQUALITY) {
            cerr << "Location::ComputeCoefConstraints -- Warning: Encountered "
                    "Strict Inequality"
                 << endl;
            cerr << "                " << (*it) << endl;

            result->add_constraint(
                Variable(coefNum + j) >=
                0);  // Just handle it as any other inequality
        }

        j++;
    }

    // Now those are all the constraints.

#ifdef __DEBUG__D_
    printPolyhedron(cout, *result, coefInfo);
#endif
    result->remove_higher_space_dimensions(
        coefNum);  // Remove the excess dimensions to obtain a new Polyhedron

    constraints = result->minimized_constraints();
    for (it = constraints.begin(); it != constraints.end(); it++) {
        cc.insertPolyStore((*it));
    }
    return;
}

void Location::ComputeCoefConstraints(C_Polyhedron& initPoly) {
    // solution for the time being
    // Just build a polyhedron with the right coefficient variables
    //   and adding dimensions for the multipliers
    // Later expunge the multipliers
    // use >= as the default constraint state.
    // First obtain the number of constraints

    // cout << endl;
    // cout << endl
    //      << "> > > Location::ComputeCoefConstraints(), Location: " << locName
    //      << "'s Initialization";

    Constraint_System constraints = poly->minimized_constraints();
    int constraintNum, coefNum;
    // count the number of multiplier variables required
    constraintNum = 0;
    for (auto it = constraints.begin(); it != constraints.end(); ++it)
        constraintNum++;
    coefNum = coefInfo->getDim();
    C_Polyhedron result(coefNum + constraintNum, UNIVERSE);
    // template coefficients in [0-coefNum-1] dimension. while \lambda_i in
    // [coefNum,coefNum+constraintNum-1] dimension
    Linear_Expression lin(0);
    int j;
    for (int i = 0; i < varsNum; i++) {
        lin = Linear_Expression(0);
        lin = lin - Variable(LIndex + i);
        j = 0;
        for (auto it = constraints.begin(); it != constraints.end(); ++it) {
            lin = lin + (*it).coefficient(Variable(i)) * Variable(coefNum + j);
            j++;
        }
        result.add_constraint(lin == 0);
    }

    lin = Linear_Expression(0);
    lin = lin - Variable(LIndex + varsNum);
    j = 0;
    for (auto it = constraints.begin(); it != constraints.end(); ++it) {
        lin = lin + (*it).inhomogeneous_term() * Variable(coefNum + j);
        j++;
    }

    result.add_constraint(lin <= 0);
    j = 0;
    for (auto it = constraints.begin(); it != constraints.end(); ++it) {
        if ((*it).type() == Constraint::NONSTRICT_INEQUALITY) {
            result.add_constraint(Variable(coefNum + j) >= 0);
        } else if ((*it).type() == Constraint::STRICT_INEQUALITY) {
            cerr << "Location::ComputeCoefConstraints -- Warning: Encountered "
                    "Strict Inequality"
                 << endl;
            cerr << "                " << (*it) << endl;
            result.add_constraint(Variable(coefNum + j) >= 0);
        }
        j++;
    }
    // project lambda and only remain c_i in the template.
    // here result record the corresponding result according to the
    // init_polyhedron [I mean the relation in c_i.] [note] it's initial part.
    // not consecution part.
    result.remove_higher_space_dimensions(coefNum);

    if (contextReady) {
        constraints = result.minimized_constraints();
        for (auto it = constraints.begin(); it != constraints.end(); ++it) {
            context->insertPolyStore((*it));
        }
    }

    initPoly.intersection_assign(result);

    // cout << endl
    //      << "< < < Location::ComputeCoefConstraints(), Location: " << locName
    //      << "'s Initialization";
    return;
}

void Location::initInv() {
    invariant = new C_Polyhedron(varsNum, UNIVERSE);
}

void Location::ExtractInvfromGenerator(Generator const& g) {
    // Extract coefficients from l to r of the generators and make a constraint
    // Add this constraint to the invariant polyhedron
    Linear_Expression lin;
    for (dimension_type i = g.space_dimension(); i-- > 0;) {
        lin += g.coefficient(Variable(i)) * Variable(i);
    }

    Linear_Expression lin1;
    int c;
    bool flag = true;
    for (int i = 0; i < varsNum; i++) {
        if (!handleInt(lin.coefficient(Variable(i)),
                       c)) {  // l+i turn to i
            flag = false;
        }
        lin1 += c * Variable(i);
    }
    if (!handleInt(lin.coefficient(Variable(varsNum)),
                   c)) {  // l+varsNum turn to varsNum
        flag = false;
    }
    lin1 += c;

    if (g.is_point() || g.is_ray()) {
        if (flag) {
            invariant->add_constraint(lin1 >= 0);
        }
    } else if (g.is_line()) {
        if (flag) {
            invariant->add_constraint(lin1 == 0);
        }
    }
}

void Location::computeInvFromGenerator(Generator const& g) {
    Linear_Expression lin;
    for (dimension_type i = g.space_dimension(); i-- > 0;) {
        lin += g.coefficient(Variable(i)) * Variable(i);
    }

    Linear_Expression lin1;
    int c;
    bool flag = true;
    for (int i = 0; i < varsNum; i++) {
        if (!handleInt(lin.coefficient(Variable(i)),
                       c)) {  // l+i turn to i
            flag = false;
        }
        lin1 += c * Variable(i);
    }
    if (!handleInt(lin.coefficient(Variable(varsNum)),
                   c)) {  // l+varsNum turn to varsNum
        flag = false;
    }
    lin1 += c;

    if (g.is_point() || g.is_ray()) {
        if (flag) {
            invariant->add_constraint(lin1 >= 0);
        }
    } else if (g.is_line()) {
        if (flag) {
            invariant->add_constraint(lin1 == 0);
        }
    }
}

void Location::ExtractInvfromGenerator(Generator_System const& generators) {
    for (auto it = generators.begin(); it != generators.end(); it++) {
        ExtractInvfromGenerator(*it);
    }
}

void Location::computeInvFromGenerator(Generator_System const& generators) {
    for (auto it = generators.begin(); it != generators.end(); it++) {
        computeInvFromGenerator(*it);
    }
}

void Location::ExtractInv(Constraint_System const& constraints) {
    C_Polyhedron res(constraints);
    Variables_Set projectSet;
    if ((int)(constraints.space_dimension()) != (varsNum + 1)) {
        for (int i = 0; i < coefInfo->getDim(); i++) {
            if (i < LIndex || i > LIndex + varsNum) {
                projectSet.insert(Variable(i));
            }
        }
        res.remove_space_dimensions(projectSet);
        // Project(res, LIndex, LIndex + (varsNum + 1));
    }
    assert(res.space_dimension() == (varsNum + 1));
    computeInvFromGenerator(res.minimized_generators());
    return;
}

void Location::addTrivial(C_Polyhedron* trivial) {
    for (int i = 0; i < varsNum; i++)
        trivial->add_constraint(Variable(LIndex + i) == 0);
    return;
}

void Location::addTrivial(C_Polyhedron& trivial) {
    for (int i = 0; i < varsNum; i++)
        trivial.add_constraint(Variable(LIndex + i) == 0);
    return;
}

void Location::ExtractAndUpdateInvOrigin(C_Polyhedron& poly,
                                         C_Polyhedron& coefPoly) {
    // cout << endl << "For location: " << locName;
    // cout << endl
    //      << "「 l: " << LIndex << ", varsNum: " << varsNum
    //      << ", coefNum: " << coefInfo->getDim() << " 」";
    ExtractInvfromGenerator(poly.minimized_generators());
    UpdateCoefCS(coefPoly);
}

void Location::ExtractAndUpdateInv(C_Polyhedron& poly, C_Polyhedron& coefPoly) {
    int coefNum = coefInfo->getDim();
    ExtractInv(poly.minimized_constraints());
    UpdateCoefCS(coefPoly);
}

void Location::contains_test(C_Polyhedron& poly,
                             C_Polyhedron& preInv,
                             C_Polyhedron& trans_rel) {
    // cout << endl << "Start contains test";
    C_Polyhedron inv_extracted(invariant->space_dimension(), UNIVERSE);
    Generator_System gs = poly.minimized_generators();
    Generator_System::const_iterator it = gs.begin();
    // cout<<endl<<"l: "<<l<<", varsNum: "<<varsNum<<endl;
    for (; it != gs.end(); it++) {
        // cout<<(*it)<<endl;
        Generator g = *it;
        // Extract coefficients from l to r of the generators and make a
        // constraint Add this constraint to the invariant polyhedron
        Linear_Expression lin;
        for (dimension_type i = g.space_dimension(); i-- > 0;) {
            lin += g.coefficient(Variable(i)) * Variable(i);
        }
        Linear_Expression lin1;
        int c;
        bool flag = true;
        for (int i = 0; i < varsNum; i++) {
            if (!handleInt(lin.coefficient(Variable(LIndex + i)), c))
                flag = false;
            lin1 += c * Variable(i);
        }
        if (!handleInt(lin.coefficient(Variable(LIndex + varsNum)), c))
            flag = false;
        lin1 += c;
        // cout<<name<<" => ";
        // print_lin_expression(cout,lin1,info);
        if (g.is_point() || g.is_ray()) {
            if (flag) {
                // invariant->add_constraint_and_minimize(lin1>=0);
                inv_extracted.add_constraint(lin1 >= 0);
            }
            // cout<<" >= 0"<<endl;
        } else if (g.is_line()) {
            if (flag) {
                // invariant->add_constraint_and_minimize(lin1==0);
                inv_extracted.add_constraint(lin1 == 0);
            }
            // cout<<" == 0"<<endl;
        }
    }

    C_Polyhedron inv_propagated(invariant->space_dimension(), UNIVERSE);
    Constraint_System cs_loc_inv = preInv.minimized_constraints();
    C_Polyhedron ph = trans_rel;
    // preInv.intersection_assign(trans_rel);
    ph.add_constraints(cs_loc_inv);
    // cout<<endl<<"ph.space_dimension: "<<ph.space_dimension();
    // cout<<endl<<"After refine "<<endl<<"   "<<ph;
    Constraint_System constraints = ph.minimized_constraints();
    C_Polyhedron result(ph.space_dimension(), UNIVERSE);
    Linear_Expression lin2(0);
    Constraint_System::const_iterator vi2;
    // cout<<endl<<"varsNum: "<<varsNum;
    for (vi2 = constraints.begin(); vi2 != constraints.end(); vi2++) {
        lin2 = Linear_Expression(0);
        for (int i = 0; i < static_cast<int>(ph.space_dimension()); i++) {
            if (i < varsNum) {
                lin2 = lin2 +
                       (*vi2).coefficient(Variable(varsNum + i)) * Variable(i);
            }
            if (varsNum <= i) {
                lin2 = lin2 +
                       (*vi2).coefficient(Variable(i - varsNum)) * Variable(i);
            }
        }
        lin2 = lin2 + (*vi2).inhomogeneous_term();
        // cout<<endl<<"Test lin: "<<lin;
        if ((*vi2).type() == Constraint::NONSTRICT_INEQUALITY) {
            result.add_constraint(lin2 >= 0);
        }
        if ((*vi2).type() == Constraint::EQUALITY) {
            result.add_constraint(lin2 == 0);
        }
    }
    // cout<<endl<<"After swap "<<endl<<"  "<<result;
    result.remove_higher_space_dimensions(varsNum);
    // cout<<endl<<"After remove higher "<<endl<<"  "<<result;
    inv_propagated.add_constraints(result.minimized_constraints());
    /*
    // add current invariants to global invariants
    Constraint_System cs_inv = result.minimized_constraints();
    C_Polyhedron poly_inv(result.space_dimension(), UNIVERSE);
    Linear_Expression lin_inv(0);
    */
    // cout<<endl<<"Invariant:"<<endl<<"   "<<*invariant;

    // if (inv_extracted.contains(inv_propagated)) {
    //     cout << endl << "inv_extracted >= inv_propagated";
    // }
    // if (inv_propagated.contains(inv_extracted)) {
    //     cout << endl << "inv_extracted <= inv_propagated";
    // }

    // cout << endl << "End contains test";
}

void Location::UpdateCoefCS(C_Polyhedron& coefPoly) {
    Constraint_System constraints = invariant->minimized_constraints();
    C_Polyhedron* result;

    int i, j, constraintNum, coefNum;

    // count the number of multiplier variables required
    constraintNum = 0;
    for (auto it = constraints.begin(); it != constraints.end(); ++it)
        constraintNum++;

    coefNum = coefInfo->getDim();

    result = new C_Polyhedron(coefNum + constraintNum, UNIVERSE);
    Linear_Expression lin(0);

    for (i = 0; i < varsNum; i++) {
        lin = Linear_Expression(0);
        lin = lin - Variable(LIndex + i);
        j = 0;
        for (auto it = constraints.begin(); it != constraints.end(); ++it) {
            lin = lin + (*it).coefficient(Variable(i)) * Variable(coefNum + j);
            j++;
        }
        result->add_constraint(lin == 0);
    }

    lin = Linear_Expression(0);
    lin = lin - Variable(LIndex + varsNum);
    j = 0;
    for (auto it = constraints.begin(); it != constraints.end(); ++it) {
        lin = lin + (*it).inhomogeneous_term() * Variable(coefNum + j);
        j++;
    }
    result->add_constraint(lin <= 0);

    j = 0;
    for (auto it = constraints.begin(); it != constraints.end(); ++it) {
        if ((*it).type() == Constraint::NONSTRICT_INEQUALITY) {
            result->add_constraint(Variable(coefNum + j) >= 0);
        } else if ((*it).type() == Constraint::STRICT_INEQUALITY) {
            cerr << "Location::ComputeCoefConstraints -- Warning: Encountered "
                    "Strict Inequality"
                 << endl;
            cerr << "                " << (*it) << endl;

            result->add_constraint(Variable(coefNum + j) >= 0);
        }
        j++;
    }
    result->remove_higher_space_dimensions(coefNum);
    coefPoly.intersection_assign(*result);
    delete (result);
}