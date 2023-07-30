
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

void Location::initialize(int vars_num,
                          var_info* info,
                          var_info* dual_info,
                          var_info* lambda_info,
                          C_Polyhedron* p,
                          string name) {
    this->vars_num = vars_num;
    this->info = info;
    this->dual_info = dual_info;
    this->lambda_info = lambda_info;
    this->poly = p;
    this->loc_name = name;
    this->loc_inv = new C_Polyhedron(vars_num, UNIVERSE);
    this->disabled_clump = new Clump(dual_info, name, "Location");
    populate_coefficients();
    invariant = new C_Polyhedron(vars_num, UNIVERSE);
    context_made = false;
    propagation_flag = false;
    ppging_flag = false;
    ppged_flag = false;
    vp_inv_flag = false;
}

void Location::initialize_without_populating(int vars_num,
                                             var_info* info,
                                             var_info* dual_info,
                                             var_info* lambda_info,
                                             C_Polyhedron* p,
                                             string name,
                                             int left_index) {
    this->vars_num = vars_num;
    this->info = info;
    this->dual_info = dual_info;
    this->lambda_info = lambda_info;
    this->poly = p;
    this->loc_name = name;
    this->loc_inv = new C_Polyhedron(vars_num, UNIVERSE);
    this->disabled_clump = new Clump(dual_info, name, "Location");
    left_index = left_index;
    invariant = new C_Polyhedron(vars_num, UNIVERSE);
    context_made = false;
    propagation_flag = false;
    ppging_flag = false;
    ppged_flag = false;
    vp_inv_flag = false;
}

Context* Location::get_context() {
    return context;
}

void Location::make_context() {
    context = new Context(info, dual_info, lambda_info);
    context_made = true;
}

Location::Location(int vars_num,
                   var_info* info,
                   var_info* dual_info,
                   var_info* lambda_info,
                   string name) {
    C_Polyhedron* init = new C_Polyhedron(vars_num, UNIVERSE);
    initialize(vars_num, info, dual_info, lambda_info, init, name);
    init_flag = false;
}

Location::Location(int vars_num,
                   var_info* info,
                   var_info* dual_info,
                   var_info* lambda_info,
                   string name,
                   int left_index) {
    C_Polyhedron* init = new C_Polyhedron(vars_num, UNIVERSE);
    initialize_without_populating(vars_num, info, dual_info, lambda_info, init,
                                  name, left_index);
    init_flag = false;
}

void Location::set_polyhedron(C_Polyhedron* q) {
    if (!init_flag) {
        poly->intersection_assign(*q);
        init_flag = true;
    } else {
        poly->poly_hull_assign(*q);
    }
}

void Location::set_initial(C_Polyhedron& q) {
    if (!init_flag) {
        poly->intersection_assign(q);
        init_flag = true;
    } else {
        poly->poly_hull_assign(q);
    }
}

C_Polyhedron* Location::get_initial() {
    return poly;
}

bool Location::has_initial() {
    return init_flag;
}

int Location::get_dimension() const {
    return vars_num;
}

const var_info* Location::get_var_info() const {
    return info;
}
const var_info* Location::get_dual_var_info() const {
    return dual_info;
}
int Location::get_range_left() const {
    return left_index;
}

void Location::add_clump(vector<Clump>& clumps) {
    // *** new-empty without disabled-path
    // Clump cl(dual_info, name, "Location");
    // ***
    // *** with disabled-path
    Clump cl = get_d_cl_reference();
    // ***
    cout << endl
         << "> > > Location::" << loc_name << " already has clump with "
         << cl.get_count() << " Polyhedra...";

    context->recursive_strategy(cl);
    cout << endl
         << "> > > Location::" << loc_name
         << " altogether pushing back clump with " << cl.get_count()
         << " Polyhedra...";

    clumps.push_back(cl);
    cout << "done";
}

bool Location::matches(string nam) const {
    return (loc_name == nam);
}

void Location::populate_coefficients() {
    left_index = dual_info->get_dimension();
    string dual_variable;
    for (int i = 0; i < vars_num; i++) {
        // dual_variable_i will be called c + location_name + i
        dual_variable = "c_" + loc_name + "_" + int_to_str(i);
        dual_info->insert(dual_variable.c_str());
    }
    dual_variable = "d_" + loc_name;
    dual_info->insert(dual_variable.c_str());
}

string const& Location::get_name() const {
    return loc_name;
}

ostream& operator<<(ostream& in, Location const& l) {
    // details of the location should go in here
    int vars_num = l.get_dimension();

    const var_info* info = l.get_var_info();
    string name = l.get_name();
    // The rest to be completed later
    in << endl;
    in << "Location: " << name << endl;
    in << "# of variables: " << vars_num << endl;
    in << "「 l: " << l.get_range_left() << ", vars_num: " << vars_num
       << ", dual_num: " << l.get_dual_var_info()->get_dimension() << " 」"
       << endl;

    if (l.initial_poly_set()) {
        in << "Initial Condition: [[ " << endl;
        in << "| " << endl;
        print_polyhedron(in, l.get_poly_reference(), info);
        in << "| " << endl;
        in << "]]" << endl;
    } else {
        in << "[ no initial condition set]" << endl;
    }

    if (name == EXIT_LOCATION && l.get_vp_inv_flag()) {
        in << "Disjunctive Invariant: [[ " << endl;
        in << "  " << endl;
        print_clump(in, l.get_vp_inv(), info);
        in << "  " << endl;
    } else {
        in << "Invariant: [[ " << endl;
        in << "| " << endl;
        print_polyhedron(in, l.GetInv(), info);
        in << "| " << endl;
    }
    in << "]]" << endl;

    return in;
}

void Location::compute_dual_constraints() {
    compute_dual_constraints(*context);
}
void Location::compute_dual_constraints(Context& cc) {
    // Inefficient solution for the time being
    // Just build a polyhedron with the right coefficient variables
    //   and adding dimensions for the multipliers
    // Later expunge the multipliers
    // use >= as the default constraint state.
    // First obtain the number of constraints
    if (!init_flag)
        return;
    Constraint_System constraints = poly->minimized_constraints();
    Constraint_System::const_iterator it;

    C_Polyhedron* result;

    int i, j, constraint_num, dual_num;

    // count the number of multiplier variables required
    constraint_num = 0;
    for (it = constraints.begin(); it != constraints.end(); ++it)
        constraint_num++;

    dual_num = dual_info->get_dimension();

    result = new C_Polyhedron(dual_num + constraint_num,
                              UNIVERSE);  // create a universe polyhedron of
                                          // dual_num +constraint_num dimensions
    Linear_Expression lin(0);

    // Now build the constraints
    for (i = 0; i < vars_num; i++) {
        lin = Linear_Expression(0);
        lin = lin - Variable(left_index + i);  // add -c_i to the constraint
        j = 0;
        for (it = constraints.begin(); it != constraints.end(); ++it) {
            lin = lin + (*it).coefficient(Variable(i)) * Variable(dual_num + j);
            j++;
        }
        result->add_constraint(lin ==
                               0);  // Add the constraint lin==0 to the result
    }

    // Now the constraints on the constant
    lin = Linear_Expression(0);
    lin = lin - Variable(left_index + vars_num);  // add -d to the constraint
    j = 0;
    for (it = constraints.begin(); it != constraints.end(); ++it) {
        lin = lin + (*it).inhomogeneous_term() * Variable(dual_num + j);
        j++;
    }

    result->add_constraint(lin <= 0);

    // Now the constraints on the multipliers

    j = 0;
    for (it = constraints.begin(); it != constraints.end(); ++it) {
        if ((*it).type() == Constraint::NONSTRICT_INEQUALITY) {
            result->add_constraint(Variable(dual_num + j) >= 0);
        } else if ((*it).type() == Constraint::STRICT_INEQUALITY) {
            cerr
                << "Location::compute_dual_constraints -- Warning: Encountered "
                   "Strict Inequality"
                << endl;
            cerr << "                " << (*it) << endl;

            result->add_constraint(
                Variable(dual_num + j) >=
                0);  // Just handle it as any other inequality
        }

        j++;
    }

    // Now those are all the constraints.

#ifdef __DEBUG__D_
    print_polyhedron(cout, *result, dual_info);
#endif
    result->remove_higher_space_dimensions(
        dual_num);  // Remove the excess dimensions to obtain a new Polyhedron

    constraints = result->minimized_constraints();
    for (it = constraints.begin(); it != constraints.end(); it++) {
        cc.add_to_poly_store((*it));
    }
    return;
}

void Location::compute_dual_constraints(C_Polyhedron& init_poly) {
    // solution for the time being
    // Just build a polyhedron with the right coefficient variables
    //   and adding dimensions for the multipliers
    // Later expunge the multipliers
    // use >= as the default constraint state.
    // First obtain the number of constraints

    cout << endl;
    cout << endl
         << "> > > Location::compute_dual_constraints(), Location: " << loc_name
         << "'s Initialization";

    // nothing to be done if polyhedra not set
    if (poly->is_empty()) {
        // the pointer p should be initialized with "new Polyhedron"
        //    the p->is_empty() means that p hasn't initialized yet.
        cout << endl
             << "< < < Initial-Value is empty in Location::" << loc_name;
        return;
    } else {
        cout << endl << "- Initial-Value is not empty: ";
        cout << endl << "  " << *poly;
    }
    if (!init_flag) {
        cout << endl << "< < < ( !polyset ) in Location::" << loc_name;
        return;
    }

    Constraint_System constraints = poly->minimized_constraints();
    int i, j, constraint_num, dual_num;
    // count the number of multiplier variables required
    constraint_num = 0;
    for (auto it = constraints.begin(); it != constraints.end(); ++it)
        constraint_num++;
    dual_num = dual_info->get_dimension();
    C_Polyhedron result(dual_num + constraint_num, UNIVERSE);
    // template coefficients in [0-dual_num-1] dimension. while \lambda_i in
    // [dual_num,dual_num+constraint_num-1] dimension
    Linear_Expression lin(0);

    for (i = 0; i < vars_num; i++) {
        lin = Linear_Expression(0);
        lin = lin - Variable(left_index + i);  // add -c_i to the constraint
        j = 0;
        for (auto it = constraints.begin(); it != constraints.end(); ++it) {
            lin = lin + (*it).coefficient(Variable(i)) * Variable(dual_num + j);
            j++;
        }
        result.add_constraint(lin ==
                              0);  // Add the constraint lin==0 to the result
    }
    // Now the constraints on the constant
    lin = Linear_Expression(0);
    lin = lin - Variable(left_index + vars_num);  // add -d to the constraint
    j = 0;
    for (auto it = constraints.begin(); it != constraints.end(); ++it) {
        lin = lin + (*it).inhomogeneous_term() * Variable(dual_num + j);
        j++;
    }

    result.add_constraint(lin <= 0);

    // Now the constraints on the multipliers

    j = 0;
    for (auto it = constraints.begin(); it != constraints.end(); ++it) {
        if ((*it).type() == Constraint::NONSTRICT_INEQUALITY) {
            result.add_constraint(Variable(dual_num + j) >= 0);
        } else if ((*it).type() == Constraint::STRICT_INEQUALITY) {
            cerr
                << "Location::compute_dual_constraints -- Warning: Encountered "
                   "Strict Inequality"
                << endl;
            cerr << "                " << (*it) << endl;
            result.add_constraint(Variable(dual_num + j) >= 0);
        }
        j++;
    }
    // project lambda and only remain c_i in the template.
    // here result record the corresponding result according to the
    // init_polyhedron [I mean the relation in c_i.] [note] it's initial part.
    //not consecution part.
    result.remove_higher_space_dimensions(dual_num);

    if (context_made) {
        constraints = result.minimized_constraints();
        for (auto it = constraints.begin(); it != constraints.end(); ++it) {
            context->add_to_poly_store((*it));
        }
    }

    init_poly.intersection_assign(result);

    cout << endl
         << "< < < Location::compute_dual_constraints(), Location: " << loc_name
         << "'s Initialization";
    return;
}

void Location::initialize_invariant() {
    invariant = new C_Polyhedron(vars_num, UNIVERSE);
}

void Location::extract_invariant_from_generator(Generator const& g) {
    // Extract coefficients from l to r of the generators and make a constraint
    // Add this constraint to the invariant polyhedron
    Linear_Expression lin;
    for (dimension_type i = g.space_dimension(); i-- > 0;) {
        lin += g.coefficient(Variable(i)) * Variable(i);
    }

    Linear_Expression lin1;
    int c;
    bool flag = true;
    for (int i = 0; i < vars_num; i++) {
        if (!handle_integers(lin.coefficient(Variable(left_index + i)), c))
            flag = false;
        lin1 += c * Variable(i);
    }
    if (!handle_integers(lin.coefficient(Variable(left_index + vars_num)), c))
        flag = false;
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

void Location::solve_invariant_from_generator(Generator const& g) {
    // cout<<endl<<"14.get here?";
    //  Extract coefficients from l to r of the generators and make a constraint
    //  Add this constraint to the invariant polyhedron

    //   cout<<endl<<"1. old_invariant: "<<endl<<"
    //   "<<invariant->minimized_generators(); cout<<endl<<"1. old_invariant:
    //   "<<endl<<"  "<<invariant->minimized_constraints();

    Linear_Expression lin;
    for (dimension_type i = g.space_dimension(); i-- > 0;) {
        lin += g.coefficient(Variable(i)) * Variable(i);
    }

    Linear_Expression lin1;
    int c;
    bool flag = true;
    for (int i = 0; i < vars_num; i++) {
        if (!handle_integers(lin.coefficient(Variable(i)),
                             c)) {  // l+i turn to i
            flag = false;
        }
        lin1 += c * Variable(i);
    }
    if (!handle_integers(lin.coefficient(Variable(vars_num)),
                         c)) {  // l+vars_num turn to vars_num
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

void Location::extract_invariant_from_generator(Generator_System const& gs) {
    Generator_System::const_iterator it = gs.begin();
    // int dual_num = dual_info->get_dimension();
    // cout<<endl<<"  「 "<<name<<", l: "<<l<<", vars_num: "<<vars_num<<",
    // dual_num: "<<dual_num<<" 」";
    for (; it != gs.end(); it++) {
        // cout<<"  "<<(*it)<<" : ";
        extract_invariant_from_generator(*it);
    }
}

void Location::solve_invariant_from_generator(Generator_System const& gs) {
    // cout<<endl<<"12.get here?";
    Generator_System::const_iterator it = gs.begin();
    // cout<<endl;
    for (; it != gs.end(); it++) {
        // cout<<endl<<"      "<<(*it)<<" : ";
        solve_invariant_from_generator(*it);
    }
    // cout<<endl<<"13.get here?";
}

void Location::extract_invariant_for_one_location_by_eliminating(
    Constraint_System const& pre_cs) {
    if ((int)(pre_cs.space_dimension()) == (vars_num + 1)) {
        C_Polyhedron Result(pre_cs);
        solve_invariant_from_generator(Result.minimized_generators());
        return;
    }

    C_Polyhedron ph(pre_cs);

    Project(ph, left_index, left_index + (vars_num + 1));
    solve_invariant_from_generator(ph.minimized_generators());

    return;
}

void Location::propagate_invariants_for_except_initial_by_propagation(
    C_Polyhedron& preloc_inv,
    C_Polyhedron& trans_rel) {
    Constraint_System cs_preloc_inv = preloc_inv.minimized_constraints();
    C_Polyhedron ph = trans_rel;
    C_Polyhedron result;

    // ph.intersection_assign(loc_inv);// Aborted: terminate called after
    // throwing an instance of 'std::invalid_argument', what():
    // PPL::C_Polyhedron::intersection_assign(y): this->space_dimension() == 4,
    // y.space_dimension() == 2.
    ph.add_constraints(cs_preloc_inv);

    cout << endl << "* After intersection " << endl << "  " << ph;
    result = swap_index_and_divide_from(ph, vars_num);
    result.remove_higher_space_dimensions(vars_num);
    invariant->intersection_assign(result);
    // invariant->add_constraints(result.minimized_constraints());

    /*
    // add current invariants to global invariants
    Constraint_System cs_inv = result.minimized_constraints();
    C_Polyhedron poly_inv(result.space_dimension(), UNIVERSE);
    Linear_Expression lin_inv(0);
    */
    cout << endl
         << "* Propagated Invariant at " << loc_name << endl
         << "  " << *invariant;
}

void Location::extract_invariant_for_initial_by_recursive_eliminating(
    Constraint_System const& pre_cs) {
    if ((int)(pre_cs.space_dimension()) == (vars_num + 1)) {
        C_Polyhedron Result(pre_cs);
        solve_invariant_from_generator(Result.minimized_generators());
        return;
    }

    //    Here is the function of
    //    "extract_invariant_for_initial_by_recursive_eliminating()" It is
    //    similar to the code in 'Farkas' part.

    int i, j, constraint_num, dual_num;
    dual_num = dual_info->get_dimension();
    Constraint_System::const_iterator it;
    Generator_System::const_iterator vj;
    cout << endl
         << "In extract_invariant_for_initial_by_recursive_eliminating(), 「 "
         << loc_name << ", l: " << left_index << ", vars_num: " << vars_num
         << ", dual_num: " << dual_num << " 」" << endl;
    cout << "- - Currently, the number of variables in Ax<=b is : "
         << pre_cs.space_dimension();
    // cout<<"- - - 1. Constraint_System constraints is "<<endl<<"
    // "<<constraints;

    //    For minimized
    C_Polyhedron ph(pre_cs);
    Constraint_System constraints = ph.minimized_constraints();

    //    1.Count the number of multiplier variables(that is generator y)
    //    required
    constraint_num = 0;
    for (it = constraints.begin(); it != constraints.end(); ++it) {
        constraint_num++;
    }
    C_Polyhedron result(
        constraint_num,
        UNIVERSE);  // create a universe polyhedron of constraint_num-dimensions
    Linear_Expression lin(0);

    //    2.Now build the constraints for y^T*A=0,
    //    here, 'A' only contains a set of coefficient of C in last location.
    for (i = 0; i < static_cast<int>(constraints.space_dimension()); i++) {
        if (static_cast<int>(constraints.space_dimension()) - (vars_num + 1) <=
            i) {  // only select the coefficient about the last set of location
            lin = Linear_Expression(0);
            j = 0;
            for (it = constraints.begin(); it != constraints.end(); ++it) {
                lin = lin - (*it).coefficient(Variable(i)) * Variable(j);
                j++;
            }
            result.add_constraint(
                lin == 0);  // Add the constraint lin==0 to the result
        }
    }
    // cout<<endl<<"- - - 2. y^T*A=0 is "<<endl<<"      "<<result;

    //    3.Now add the constraints on the multipliers
    j = 0;
    for (it = constraints.begin(); it != constraints.end(); ++it) {
        if ((*it).type() == Constraint::NONSTRICT_INEQUALITY) {
            //  Set y>=0 if Ax <= b
            result.add_constraint(Variable(j) >= 0);
        } else if ((*it).type() == Constraint::EQUALITY) {
            //  Do nothing if Ax == b
        }
        j++;
    }
    //    Now those are all the constraints.
    // cout<<endl<<"- - - 3. y^T*A=0 (added some y>=0) is "<<endl<<" "<<result;
    cout << endl
         << "- - - 4. y^T*A=0 's minimized_constraints() is " << endl
         << "      " << result.minimized_constraints();

    //    For minimized
    Constraint_System test_cs = result.minimized_constraints();
    C_Polyhedron result1(test_cs);
    //    Test for cout
    int test_nc1 = 0;
    for (it = test_cs.begin(); it != test_cs.end(); ++it) {
        test_nc1++;
    }
    cout << endl
         << "* * * The number of constraints(minimized) in 'y^T*A == 0': "
         << test_nc1;
    cout << endl
         << "* * * The number of variables in 'y': "
         << "「 " << test_cs.space_dimension() << " 」";
    cout << endl
         << "* * * The number of variables to be eliminated in 'A': "
         << (vars_num + 1);

    //    5.After we get y^T*A=0, then transfer from the generator of y^T to
    //    values of y^T
    // cout<<endl<<"- - - 5. y^T 's generators() is "<<endl<<"
    // "<<result1.generators(); cout<<endl<<"- - - 6. y^T 's
    // minimized_generators() is "<<endl<<" "<<result1.minimized_generators();
    Generator_System gs = result1.minimized_generators();
    C_Polyhedron result2(constraints.space_dimension() - (vars_num + 1),
                         UNIVERSE);  // Store y^T*b>=0
    for (vj = gs.begin(); vj != gs.end(); vj++) {
        Generator g = (*vj);
        vector<int> y(constraint_num, -999);
        // cout<<endl<<"[ ";
        for (dimension_type i = 0; i < g.space_dimension(); i++) {
            handle_integers(g.coefficient(Variable(i)), y[i]);
            // cout<<y[i]<<", ";
        }
        // cout<<"]";
        //     Now, y^T are extracted.

        //    6.Now build the constraints for y^T*b>=0
        //    here, 'b' contains the remained set of coefficient of C except the
        //    locations in 'A'.
        Linear_Expression lin1(0);
        j = 0;
        for (it = constraints.begin(); it != constraints.end(); ++it) {
            for (i = 0; i < static_cast<int>(constraints.space_dimension());
                 i++) {
                if (i < static_cast<int>(constraints.space_dimension()) -
                            (vars_num + 1)) {
                    lin1 = lin1 +
                           y[j] * (*it).coefficient(Variable(left_index + i)) *
                               Variable(i);  // second l+i turn to i
                }
            }
            j++;
        }
        result2.add_constraint(lin1 >= 0);
        // cout<<endl<<"- - - 7. y^T*b>=0(added in the loop) is
        // "<<endl<<result2<<endl;
        //     Now result2 contains the constraints of b( coefficient of
        //     invariant)
    }
    // cout<<endl<<"- - - 8. y^T*b>=0 is "<<endl<<"      "<<result2;

    //    For minimized
    Constraint_System cs1 = result2.minimized_constraints();
    C_Polyhedron result3(cs1);
    cout << endl
         << "- - - 9. y^T*b>=0 's minimized_constraints is " << endl
         << "      " << result3;

    //    Test for cout
    int test_nc2 = 0;
    for (it = cs1.begin(); it != cs1.end(); ++it) {
        test_nc2++;
    }
    cout << endl
         << "* * * The number of constraints(minimized) in 'y^T*b >= 0': "
         << test_nc2;
    cout << endl
         << "* * * The number of variables to be eliminated in 'b': "
         << "「 " << cs1.space_dimension() << " 」" << endl;
    // cout<<endl<<"- - - 10. y^T*b>=0 's minimized_generators is "<<endl<<"
    // "<<result3.minimized_generators()<<endl;

    extract_invariant_for_initial_by_recursive_eliminating(
        result3.minimized_constraints());

    cout << endl;
    return;
}

void Location::add_to_trivial(C_Polyhedron* trivial) {
    for (int i = 0; i < vars_num; i++)
        trivial->add_constraint(Variable(left_index + i) == 0);
    return;
}

void Location::add_to_trivial(C_Polyhedron& trivial) {
    // add c_l=0
    for (int i = 0; i < vars_num; i++)
        // trivial.add_constraint_and_minimize(Variable(l+i)==0);
        trivial.add_constraint(Variable(left_index + i) == 0);
    return;
}

void Location::extract_invariants_and_update(C_Polyhedron& pp,
                                             C_Polyhedron& dualp) {
    cout << endl << "For location: " << loc_name;
    cout << endl
         << "「 l: " << left_index << ", vars_num: " << vars_num
         << ", dual_num: " << dual_info->get_dimension() << " 」";
    extract_invariant_from_generator(pp.minimized_generators());
    update_dual_constraints(dualp);
}

void Location::extract_invariants_and_update_for_one_location_by_eliminating(
    C_Polyhedron& pp,
    C_Polyhedron& dualp) {
    // cout<<endl<<"- In
    // extract_invariants_and_update_for_one_location_by_eliminating()";
    // cout<<endl<<"- Before
    // extract_invariant_for_one_location_by_eliminating()"; cout<<endl;
    int dual_num = dual_info->get_dimension();
    cout << endl << "For location: " << loc_name;
    cout << endl
         << "「 l: " << left_index << ", vars_num: " << vars_num
         << ", dual_num: " << dual_num << " 」";
    // cout<<endl<<"C_Polyhedron & pp is "<<endl<<"    "<<pp;
    if (projection == "no_projection") {
        cout << endl << "Do not use projection";
        extract_invariant_from_generator(pp.minimized_generators());
    } else {
        extract_invariant_for_one_location_by_eliminating(
            pp.minimized_constraints());
    }
    update_dual_constraints(dualp);
}

void Location::
    propagate_invariants_and_update_for_except_initial_by_propagation(
        C_Polyhedron& preloc_inv,
        C_Polyhedron& trans_rel /*, C_Polyhedron & dualp*/) {
    cout << endl << "= Doing Propagation at Location " << loc_name;
    cout << endl << "= Location invariant " << endl << "  " << preloc_inv;
    cout << endl << "= Transition relation " << endl << "  " << trans_rel;
    propagate_invariants_for_except_initial_by_propagation(preloc_inv,
                                                           trans_rel);
    // update_dual_constraints(dualp);
}

void Location::contains_test(C_Polyhedron& pp,
                             C_Polyhedron& loc_inv,
                             C_Polyhedron& trans_rel) {
    cout << endl << "Start contains test";
    C_Polyhedron inv_extracted(invariant->space_dimension(), UNIVERSE);
    Generator_System gs = pp.minimized_generators();
    Generator_System::const_iterator it = gs.begin();
    // cout<<endl<<"l: "<<l<<", vars_num: "<<vars_num<<endl;
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
        for (int i = 0; i < vars_num; i++) {
            if (!handle_integers(lin.coefficient(Variable(left_index + i)), c))
                flag = false;
            lin1 += c * Variable(i);
        }
        if (!handle_integers(lin.coefficient(Variable(left_index + vars_num)),
                             c))
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
    Constraint_System cs_loc_inv = loc_inv.minimized_constraints();
    C_Polyhedron ph = trans_rel;
    // loc_inv.intersection_assign(trans_rel);
    ph.add_constraints(cs_loc_inv);
    // cout<<endl<<"ph.space_dimension: "<<ph.space_dimension();
    // cout<<endl<<"After refine "<<endl<<"   "<<ph;
    Constraint_System constraints = ph.minimized_constraints();
    C_Polyhedron result(ph.space_dimension(), UNIVERSE);
    Linear_Expression lin2(0);
    Constraint_System::const_iterator vi2;
    // cout<<endl<<"vars_num: "<<vars_num;
    for (vi2 = constraints.begin(); vi2 != constraints.end(); vi2++) {
        lin2 = Linear_Expression(0);
        for (int i = 0; i < static_cast<int>(ph.space_dimension()); i++) {
            if (i < vars_num) {
                lin2 = lin2 +
                       (*vi2).coefficient(Variable(vars_num + i)) * Variable(i);
            }
            if (vars_num <= i) {
                lin2 = lin2 +
                       (*vi2).coefficient(Variable(i - vars_num)) * Variable(i);
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
    result.remove_higher_space_dimensions(vars_num);
    // cout<<endl<<"After remove higher "<<endl<<"  "<<result;
    inv_propagated.add_constraints(result.minimized_constraints());
    /*
    // add current invariants to global invariants
    Constraint_System cs_inv = result.minimized_constraints();
    C_Polyhedron poly_inv(result.space_dimension(), UNIVERSE);
    Linear_Expression lin_inv(0);
    */
    // cout<<endl<<"Invariant:"<<endl<<"   "<<*invariant;

    if (inv_extracted.contains(inv_propagated)) {
        cout << endl << "inv_extracted >= inv_propagated";
    }
    if (inv_propagated.contains(inv_extracted)) {
        cout << endl << "inv_extracted <= inv_propagated";
    }

    cout << endl << "End contains test";
}

void Location::
    extract_invariants_and_update_for_initial_by_recursive_eliminating(
        C_Polyhedron& pp,
        C_Polyhedron& dualp) {
    // cout<<endl<<"- In
    // extract_invariants_and_update_for_initial_by_recursive_eliminating()";
    // cout<<endl<<"- Before
    // extract_invariant_for_initial_by_recursive_eliminating()";
    // cout<<endl<<"-
    // - C_Polyhedron & pp is "<<endl<<"    "<<pp; cout<<endl<<"- -
    // C_Polyhedron pp.constraints() is "<<endl<<"    "<<pp.constraints()<<endl;
    extract_invariant_for_initial_by_recursive_eliminating(
        pp.minimized_constraints());
    update_dual_constraints(dualp);
}

void Location::update_dual_constraints(C_Polyhedron& dualp) {
    // cout<<endl<<"> > > In update_dual_constraints(C_Polyhedron & dualp),
    // Location : "<<name;

    // now add the invariant information back to dualp
    Constraint_System constraints = invariant->minimized_constraints();
    Constraint_System::const_iterator it;
    C_Polyhedron* result;

    int i, j, constraint_num, dual_num;

    // count the number of multiplier variables required
    constraint_num = 0;
    for (it = constraints.begin(); it != constraints.end(); ++it)
        constraint_num++;

    dual_num = dual_info->get_dimension();

    result = new C_Polyhedron(dual_num + constraint_num,
                              UNIVERSE);  // create a universe polyhedron of
                                          // dual_num +constraint_num dimensions
    Linear_Expression lin(0);

    // Now build the constraints
    for (i = 0; i < vars_num; i++) {
        lin = Linear_Expression(0);
        lin = lin - Variable(left_index + i);  // add -c_i to the constraint
        j = 0;
        for (it = constraints.begin(); it != constraints.end(); ++it) {
            lin = lin + (*it).coefficient(Variable(i)) * Variable(dual_num + j);
            j++;
        }
        result->add_constraint(lin ==
                               0);  // Add the constraint lin==0 to the result
    }

    // Now the constraints on the constant
    lin = Linear_Expression(0);
    lin = lin - Variable(left_index + vars_num);  // add -d to the constraint
    j = 0;
    for (it = constraints.begin(); it != constraints.end(); ++it) {
        lin = lin + (*it).inhomogeneous_term() * Variable(dual_num + j);
        j++;
    }
    result->add_constraint(lin <= 0);

    // Now the constraints on the multipliers

    j = 0;
    for (it = constraints.begin(); it != constraints.end(); ++it) {
        if ((*it).type() == Constraint::NONSTRICT_INEQUALITY) {
            result->add_constraint(Variable(dual_num + j) >= 0);
        } else if ((*it).type() == Constraint::STRICT_INEQUALITY) {
            cerr
                << "Location::compute_dual_constraints -- Warning: Encountered "
                   "Strict Inequality"
                << endl;
            cerr << "                " << (*it) << endl;

            result->add_constraint(
                Variable(dual_num + j) >=
                0);  // Just handle it as any other inequality
        }
        j++;
    }
    // Now those are all the constraints.

    // contains_test(*result, dual_num);
    //  * * *
    //  Old method
    result->remove_higher_space_dimensions(
        dual_num);  // Remove the excess dimensions to obtain a new Polyhedron
    // * * *
    // * * *
    // New method
    // eliminate_by_Farkas(*result, dual_num);
    // * * *

    dualp.intersection_assign(*result);
    delete (result);

    // cout<<endl<<"      "<<"After update_dual_constraints, dualp is ";
    // cout<<endl<<"      "<<dualp;
    // cout<<endl<<"< < < Out update_dual_constraints(C_Polyhedron & dualp),
    // Location : "<<name<<endl;
}

void Location::extract_invariants_and_update_by_binary_eliminating(
    C_Polyhedron& pp,
    C_Polyhedron& dualp) {
    // cout<<endl<<"10.get here?";
    solve_invariant_from_generator(pp.minimized_generators());
    // cout<<endl<<"11.get here?";
    update_dual_constraints(dualp);
}