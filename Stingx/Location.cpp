
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
extern int debug_2;
extern int debug_3;

void Location::initialize(int n,
                          var_info* f,
                          var_info* fd,
                          var_info* fm,
                          C_Polyhedron* p,
                          string name) {
    this->n = n;
    this->f = f;
    this->fd = fd;
    this->fm = fm;
    this->p = p;
    this->name = name;
    this->loc_inv = new C_Polyhedron(n, UNIVERSE);
    this->d_cl = new Clump(
        fd, name, "Location");  // disabled path; added by Hongming, at Shanghai
                                // Jiao Tong University, 2022/09/20
    populate_coefficients();
    invariant = new C_Polyhedron(n, UNIVERSE);
    context_made = false;
    propagation_flag = false;
    ppging_flag = false;
    ppged_flag = false;
    vp_inv_flag = false;
}

void Location::initialize_without_populating(int n,
                                             var_info* f,
                                             var_info* fd,
                                             var_info* fm,
                                             C_Polyhedron* p,
                                             string name,
                                             int left) {
    this->n = n;
    this->f = f;
    this->fd = fd;
    this->fm = fm;
    this->p = p;
    this->name = name;
    this->loc_inv = new C_Polyhedron(n, UNIVERSE);
    this->d_cl = new Clump(
        fd, name, "Location");  // disabled path; added by Hongming, at Shanghai
                                // Jiao Tong University, 2022/09/20
    l = left;
    invariant = new C_Polyhedron(n, UNIVERSE);
    context_made = false;
    propagation_flag = false;
    ppging_flag = false;
    ppged_flag = false;
    vp_inv_flag = false;
}

Context* Location::get_context() {
    return c;
}

void Location::make_context() {
    c = new Context(f, fd, fm);
    context_made = true;
}

Location::Location(int n,
                   var_info* f,
                   var_info* fd,
                   var_info* fm,
                   C_Polyhedron* p,
                   string name) {
    initialize(n, f, fd, fm, p, name);
    polyset = true;
}

Location::Location(int n,
                   var_info* f,
                   var_info* fd,
                   var_info* fm,
                   string name) {
    C_Polyhedron* init = new C_Polyhedron(n, UNIVERSE);
    initialize(n, f, fd, fm, init, name);
    polyset = false;
}

Location::Location(int n,
                   var_info* f,
                   var_info* fd,
                   var_info* fm,
                   string name,
                   int left) {
    C_Polyhedron* init = new C_Polyhedron(n, UNIVERSE);
    initialize_without_populating(n, f, fd, fm, init, name, left);
    polyset = false;
}

Location::Location(int n,
                   var_info* f,
                   var_info* fd,
                   var_info* fm,
                   C_Polyhedron* p,
                   string name,
                   int left) {
    initialize_without_populating(n, f, fd, fm, p, name, left);

    polyset = true;
}

void Location::set_polyhedron(C_Polyhedron* q) {
    if (!polyset) {
        p->intersection_assign(*q);
        polyset = true;
    } else {
        // p->poly_hull_assign_and_minimize(*q);
        p->poly_hull_assign(*q);
    }
}

void Location::set_initial(C_Polyhedron& q) {
    if (!polyset) {
        p->intersection_assign(q);
        polyset = true;
    } else {
        p->poly_hull_assign(q);
    }
}

C_Polyhedron* Location::get_initial() {
    return p;
}

bool Location::has_initial() {
    return polyset;
}

int Location::get_dimension() const {
    return n;
}

const var_info* Location::get_var_info() const {
    return f;
}
const var_info* Location::get_dual_var_info() const {
    return fd;
}
int Location::get_range_left() const {
    return l;
}

void Location::add_clump(vector<Clump>& vcl) {
    // *** new-empty without disabled-path
    // Clump cl(fd, name, "Location");
    // ***
    // *** with disabled-path
    Clump cl = get_d_cl_reference();
    // ***
    cout << endl
         << "> > > Location::" << name << " already has clump with "
         << cl.get_count() << " Polyhedra...";
    // if (debug_2) {
    //     cout << endl << "- cl.print_clump(): ";
    //     cl.print_vector_of_poly();
    // }
    // cout<<"- The Root Context: "<<endl<<(*c)<<endl;
    c->recursive_strategy(cl);
    cout << endl
         << "> > > Location::" << name << " altogether pushing back clump with "
         << cl.get_count() << " Polyhedra...";
    if (debug_2) {
        cout << endl << "- cl.print_clump(): ";
        cl.print_vector_of_poly();
    }
    vcl.push_back(cl);
    cout << "done";
}

bool Location::matches(string nam) const {
    return (name == nam);
}

void Location::populate_coefficients() {
    l = fd->get_dimension();
    int i;
    string dvi;
    for (i = 0; i < n; i++) {
        // dual_variable_i will be called c + location_name + i
        dvi = "c_" + name + "_" + int_to_str(i);
        fd->insert(dvi.c_str());
    }
    dvi = "d_" + name;
    fd->insert(dvi.c_str());
}

string const& Location::get_name() const {
    return name;
}

ostream& operator<<(ostream& in, Location const& l) {
    // details of the location should go in here
    int n = l.get_dimension();

    const var_info* f = l.get_var_info();
    string name = l.get_name();
    // The rest to be completed later
    in << endl;
    in << "Location: " << name << endl;
    in << "# of variables: " << n << endl;
    in << "「 l: " << l.get_range_left() << ", n: " << n
       << ", nd: " << l.get_dual_var_info()->get_dimension() << " 」" << endl;
    
    if (l.initial_poly_set()) {
        in << "Initial Condition: [[ " << endl;
        in << "| " << endl;
        print_polyhedron(in, l.get_poly_reference(), f);
        in << "| " << endl;
        in << "]]" << endl;
    } else {
        in << "[ no initial condition set]" << endl;
    }

    if (name == EXIT_LOCATION && l.get_vp_inv_flag()) {
        in << "Disjunctive Invariant: [[ " << endl;
        in << "  " << endl;
        print_clump(in, l.get_vp_inv(), f);
        in << "  " << endl;
    } else {
        in << "Invariant: [[ " << endl;
        in << "| " << endl;
        print_polyhedron(in, l.get_invariant(), f);
        in << "| " << endl;
    }
    in << "]]" << endl;

    return in;
}

void Location::compute_dual_constraints() {
    compute_dual_constraints(*c);
}
void Location::compute_dual_constraints(Context& cc) {
    // Inefficient solution for the time being
    // Just build a polyhedron with the right coefficient variables
    //   and adding dimensions for the multipliers
    // Later expunge the multipliers
    // use >= as the default constraint state.
    // First obtain the number of constraints
    if (!polyset)
        return;
    Constraint_System cs = p->minimized_constraints();
    Constraint_System::const_iterator vi;

    C_Polyhedron* result;

    int i, j, nc, nd;

    // count the number of multiplier variables required
    nc = 0;
    for (vi = cs.begin(); vi != cs.end(); ++vi)
        nc++;

    nd = fd->get_dimension();

    result = new C_Polyhedron(
        nd + nc,
        UNIVERSE);  // create a universe polyhedron of nd +nc dimensions
    Linear_Expression lin(0);

    // Now build the constraints
    for (i = 0; i < n; i++) {
        lin = Linear_Expression(0);
        lin = lin - Variable(l + i);  // add -c_i to the constraint
        j = 0;
        for (vi = cs.begin(); vi != cs.end(); ++vi) {
            lin = lin + (*vi).coefficient(Variable(i)) * Variable(nd + j);
            j++;
        }
        result->add_constraint(lin ==
                               0);  // Add the constraint lin==0 to the result
    }

    // Now the constraints on the constant
    lin = Linear_Expression(0);
    lin = lin - Variable(l + n);  // add -d to the constraint
    j = 0;
    for (vi = cs.begin(); vi != cs.end(); ++vi) {
        lin = lin + (*vi).inhomogeneous_term() * Variable(nd + j);
        j++;
    }

    result->add_constraint(lin <= 0);

    // Now the constraints on the multipliers

    j = 0;
    for (vi = cs.begin(); vi != cs.end(); ++vi) {
        if ((*vi).type() == Constraint::NONSTRICT_INEQUALITY) {
            result->add_constraint(Variable(nd + j) >= 0);
        } else if ((*vi).type() == Constraint::STRICT_INEQUALITY) {
            cerr
                << "Location::compute_dual_constraints -- Warning: Encountered "
                   "Strict Inequality"
                << endl;
            cerr << "                " << (*vi) << endl;

            result->add_constraint(
                Variable(nd + j) >=
                0);  // Just handle it as any other inequality
        }

        j++;
    }

    // Now those are all the constraints.

#ifdef __DEBUG__D_
    print_polyhedron(cout, *result, fd);
#endif
    result->remove_higher_space_dimensions(
        nd);  // Remove the excess dimensions to obtain a new Polyhedron

    cs = result->minimized_constraints();
    for (vi = cs.begin(); vi != cs.end(); vi++) {
        cc.add_to_poly_store((*vi));
    }
    return;
}

void Location::compute_dual_constraints(C_Polyhedron& initp) {
    // solution for the time being
    // Just build a polyhedron with the right coefficient variables
    //   and adding dimensions for the multipliers
    // Later expunge the multipliers
    // use >= as the default constraint state.
    // First obtain the number of constraints

    cout << endl;
    cout << endl
         << "> > > Location::compute_dual_constraints(), Location: " << name
         << "'s Initialization";

    // nothing to be done if polyhedra not set
    if (p->is_empty()) {
        // the pointer p should be initialized with "new Polyhedron"
        //    the p->is_empty() means that p hasn't initialized yet.
        cout << endl << "< < < Initial-Value is empty in Location::" << name;
    } else {
        cout << endl << "- Initial-Value is not empty: ";
        cout << endl << "  " << *p;
    }
    if (!polyset) {
        cout << endl << "< < < ( !polyset ) in Location::" << name;
        return;
    }
    if (p->is_empty()) {
        return;
    }
    Constraint_System cs = p->minimized_constraints();
    Constraint_System::const_iterator vi;
    int i, j, nc, nd;
    // count the number of multiplier variables required
    nc = 0;
    for (vi = cs.begin(); vi != cs.end(); ++vi)
        nc++;
    nd = fd->get_dimension();
    if (debug_2) {
        cout << endl << "------------------------------";
        cout << endl << "- input_cs: " << endl << "  " << cs;
    }

    C_Polyhedron result(
        nd + nc,
        UNIVERSE);  // create a universe polyhedron of nd +nc dimensions
    Linear_Expression lin(0);

    // Now build the constraints
    for (i = 0; i < n; i++) {
        lin = Linear_Expression(0);
        lin = lin - Variable(l + i);  // add -c_i to the constraint
        j = 0;
        for (vi = cs.begin(); vi != cs.end(); ++vi) {
            lin = lin + (*vi).coefficient(Variable(i)) * Variable(nd + j);
            j++;
        }
        result.add_constraint(lin ==
                              0);  // Add the constraint lin==0 to the result
    }

    // Now the constraints on the constant
    lin = Linear_Expression(0);
    lin = lin - Variable(l + n);  // add -d to the constraint
    j = 0;
    for (vi = cs.begin(); vi != cs.end(); ++vi) {
        lin = lin + (*vi).inhomogeneous_term() * Variable(nd + j);
        j++;
    }

    result.add_constraint(lin <= 0);

    // Now the constraints on the multipliers

    j = 0;
    for (vi = cs.begin(); vi != cs.end(); ++vi) {
        if ((*vi).type() == Constraint::NONSTRICT_INEQUALITY) {
            result.add_constraint(Variable(nd + j) >= 0);
        } else if ((*vi).type() == Constraint::STRICT_INEQUALITY) {
            cerr
                << "Location::compute_dual_constraints -- Warning: Encountered "
                   "Strict Inequality"
                << endl;
            cerr << "                " << (*vi) << endl;
            result.add_constraint(Variable(nd + j) >=
                                  0);  // Just handle it as any other inequality
        }
        j++;
    }

    // Now those are all the constraints.

#ifdef __DEBUG__D_
    print_polyhedron(cout, result, fd);
#endif

    if (debug_2) {
        cout << endl << "------------------------------";
        cout << endl
             << "- Farkas_Initialization_Poly (before projection): " << endl
             << "  " << result.minimized_constraints();
    }
    // contains_test(result, nd);
    // Timer test_time_for_remove_higher_space_dimensions;
    //  * * *
    //  Old method for eliminate lambda
    result.remove_higher_space_dimensions(
        nd);  // Remove the excess dimensions to obtain a new Polyhedron
    // * * *
    // * * *
    // New method for eliminate lambda: Farkas' Lemma 2.5a, Ax<=b
    // eliminate_by_Farkas(result, nd);
    // * * *
    // test_time_for_remove_higher_space_dimensions.stop();
    // cout<<endl<<"- The remove_higher_space_dimensions(in location) Time
    // Taken is :
    // "<<test_time_for_remove_higher_space_dimensions.compute_time_elapsed()<<endl;
    if (debug_2) {
        cout << endl << "------------------------------";
        cout << endl
             << "- Farkas_Initialization_Poly (after projection): " << endl
             << "  " << result.minimized_constraints();
    }

    // now add result
    if (context_made) {
        cs = result.minimized_constraints();
        for (vi = cs.begin(); vi != cs.end(); ++vi) {
            c->add_to_poly_store((*vi));
        }
    }

    initp.intersection_assign(result);

    cout << endl
         << "< < < Location::compute_dual_constraints(), Location: " << name
         << "'s Initialization";
    return;
}

void Location::initialize_invariant() {
    invariant = new C_Polyhedron(n, UNIVERSE);
}

void Location::extract_invariant_from_generator(Generator const& g) {
    // Extract coefficients from l to r of the generators and make a constraint
    // Add this constraint to the invariant polyhedron

    if (debug_2) {
        cout << endl << "------------------------------";
        cout << endl << "- generator: " << g;
        if (g.is_point()) {
            cout << endl << "  g.is_point()";
        } else if (g.is_ray()) {
            cout << endl << "  g.is_ray()";
        } else if (g.is_line()) {
            cout << endl << "  g.is_line()";
        } else {
            cout << endl << "  g is not point, not ray, not line";
        }
    }
    Linear_Expression lin;
    for (dimension_type i = g.space_dimension(); i-- > 0;) {
        lin += g.coefficient(Variable(i)) * Variable(i);
    }
    if (debug_2) {
        cout << endl << "  lin: " << lin;
    }

    Linear_Expression lin1;
    int c;
    bool flag = true;
    for (int i = 0; i < n; i++) {
        if (!handle_integers(lin.coefficient(Variable(l + i)), c))
            flag = false;
        lin1 += c * Variable(i);
    }
    if (!handle_integers(lin.coefficient(Variable(l + n)), c))
        flag = false;
    lin1 += c;

    if (debug_2) {
        cout << endl
             << "- Location.invariant(before adding lin1): " << endl
             << "  " << (*invariant);
        cout << endl << "- lin1: " << name << " => " << endl << "  ";
        print_pure_lin_expression(lin1, f);
    }
    if (g.is_point() || g.is_ray()) {
        if (debug_2) {
            cout << " >= 0";
        }
        if (flag) {
            if (debug_2) {
                cout << endl << "- invariant->add_constraint(lin1>=0)";
            }
            // invariant->add_constraint_and_minimize(lin1>=0);
            invariant->add_constraint(lin1 >= 0);
        } else {
            if (debug_2) {
                cout << endl << "- invariant does not add_constraint(lin1>=0)";
            }
        }
    } else if (g.is_line()) {
        if (debug_2) {
            cout << " == 0";
        }
        if (flag) {
            if (debug_2) {
                cout << endl << "- invariant->add_constraint(lin1==0)";
            }
            // invariant->add_constraint_and_minimize(lin1==0);
            invariant->add_constraint(lin1 == 0);
        } else {
            if (debug_2) {
                cout << endl << "- invariant does not add_constraint(lin1==0)";
            }
        }
    }
    if (debug_2) {
        cout << endl
             << "- Location.invariant(after adding lin1): " << endl
             << "  " << (*invariant);
    }
}

void Location::solve_invariant_from_generator(Generator const& g) {
    // cout<<endl<<"14.get here?";
    //  Extract coefficients from l to r of the generators and make a constraint
    //  Add this constraint to the invariant polyhedron

    //   cout<<endl<<"1. old_invariant: "<<endl<<"
    //   "<<invariant->minimized_generators(); cout<<endl<<"1. old_invariant:
    //   "<<endl<<"  "<<invariant->minimized_constraints();

    if (debug_2) {
        cout << endl << "------------------------------";
        cout << endl << "- generator: " << g;
        if (g.is_point()) {
            cout << endl << "  g.is_point()";
        } else if (g.is_ray()) {
            cout << endl << "  g.is_ray()";
        } else if (g.is_line()) {
            cout << endl << "  g.is_line()";
        } else {
            cout << endl << "  g is not point, not ray, not line";
        }
    }
    Linear_Expression lin;
    for (dimension_type i = g.space_dimension(); i-- > 0;) {
        lin += g.coefficient(Variable(i)) * Variable(i);
    }
    if (debug_2) {
        cout << endl << "  lin: " << lin;
    }

    Linear_Expression lin1;
    int c;
    bool flag = true;
    for (int i = 0; i < n; i++) {
        if (!handle_integers(lin.coefficient(Variable(i)),
                             c)) {  // l+i turn to i
            flag = false;
        }
        lin1 += c * Variable(i);
    }
    if (!handle_integers(lin.coefficient(Variable(n)), c)) {  // l+n turn to n
        flag = false;
    }
    lin1 += c;

    if (debug_2) {
        cout << endl
             << "- Location.invariant(before adding lin1): " << endl
             << "  " << (*invariant);
        cout << endl << "- lin1: " << name << " => " << endl << "  ";
        print_pure_lin_expression(lin1, f);
    }
    if (g.is_point() || g.is_ray()) {
        if (debug_2) {
            cout << " >= 0";
        }
        if (flag) {
            if (debug_2) {
                cout << endl << "- invariant->add_constraint(lin1>=0)";
            }
            // invariant->add_constraint_and_minimize(lin1>=0);
            invariant->add_constraint(lin1 >= 0);
        } else {
            if (debug_2) {
                cout << endl << "- invariant does not add_constraint(lin1>=0)";
            }
        }
    } else if (g.is_line()) {
        if (debug_2) {
            cout << " == 0";
        }
        if (flag) {
            if (debug_2) {
                cout << endl << "- invariant->add_constraint(lin1==0)";
            }
            // invariant->add_constraint_and_minimize(lin1==0);
            invariant->add_constraint(lin1 == 0);
        } else {
            if (debug_2) {
                cout << endl << "- invariant does not add_constraint(lin1==0)";
            }
        }
    }
    // cout<<endl<<"15.get here?";
    //    cout<<endl<<"1. invariant: "<<endl<<"
    //    "<<invariant->minimized_generators(); cout<<endl<<"1. invariant:
    //    "<<endl<<"  "<<invariant->minimized_constraints();
    if (debug_2) {
        cout << endl
             << "- Location.invariant(after adding lin1): " << endl
             << "  " << (*invariant);
    }
}

void Location::extract_invariant_from_generator(Generator_System const& gs) {
    Generator_System::const_iterator vi = gs.begin();
    // int nd = fd->get_dimension();
    // cout<<endl<<"  「 "<<name<<", l: "<<l<<", n: "<<n<<", nd: "<<nd<<" 」";
    for (; vi != gs.end(); vi++) {
        // cout<<"  "<<(*vi)<<" : ";
        extract_invariant_from_generator(*vi);
    }
}

void Location::solve_invariant_from_generator(Generator_System const& gs) {
    // cout<<endl<<"12.get here?";
    Generator_System::const_iterator vi = gs.begin();
    // cout<<endl;
    for (; vi != gs.end(); vi++) {
        // cout<<endl<<"      "<<(*vi)<<" : ";
        solve_invariant_from_generator(*vi);
    }
    // cout<<endl<<"13.get here?";
}

void Location::extract_invariant_for_one_location_by_eliminating(
    Constraint_System const& pre_cs) {
    if ((int)(pre_cs.space_dimension()) == (n + 1)) {
        C_Polyhedron Result(pre_cs);
        if (debug_2) {
            cout << endl << "------------------------------";
            cout << endl
                 << "- cpoly.constraints: " << endl
                 << "  " << Result.minimized_constraints();
            cout << endl
                 << "- cpoly.generators: " << endl
                 << "  " << Result.minimized_generators();
        }
        solve_invariant_from_generator(Result.minimized_generators());
        return;
    }

    //    Here is the function of
    //    "extract_invariant_for_one_location_by_eliminating()" It is similar to
    //    the code in 'Farkas' part.

    // int i, j, nc, nd;
    // nd = fd->get_dimension();

    C_Polyhedron ph(pre_cs);
    // cout<<endl;
    // cout<<endl<<"In extract_invariant_for_one_location_by_eliminating(), 「
    // "<<name<<", l: "<<l<<", n: "<<n<<", nd: "<<nd<<" 」"; contains_test(ph,
    // n+1);
    //  * * *
    //  New method, eliminate Ax<=b by remove_higher_space_dimension
    // ph.remove_higher_space_dimensions(n+1);
    //  * * *
    //  New method, eliminate Ax<=b by Farkas
    // Project_by_Farkas(ph, l, l+(n+1));
    //  * * *
    //  New method, eliminate Ax<=b by Kohler
    // Project_by_Kohler(ph, l, l+(n+1) );
    //  * * *
    Project(ph, l, l + (n + 1));
    // cout<<endl<<"After eliminate by Projection, the poly is "<<endl<<"
    // "<<ph;

    if (debug_2) {
        cout << endl << "------------------------------";
        cout << endl
             << "- cpoly(projected).constraints: " << endl
             << "  " << ph.minimized_constraints();
        cout << endl
             << "- cpoly(projected).generators: " << endl
             << "  " << ph.minimized_generators();
    }
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
    if (debug_3) {
        cout << endl
             << "* C_Polyhedron.space_dimension: " << ph.space_dimension();
    }
    cout << endl << "* After intersection " << endl << "  " << ph;
    result = swap_index_and_divide_from(ph, n);
    if (debug_2) {
        cout << endl << "* After swap " << endl << "  " << result;
    }
    result.remove_higher_space_dimensions(n);
    if (debug_2) {
        cout << endl << "* After remove higher " << endl << "  " << result;
    }
    invariant->intersection_assign(result);
    // invariant->add_constraints(result.minimized_constraints());

    /*
    // add current invariants to global invariants
    Constraint_System cs_inv = result.minimized_constraints();
    C_Polyhedron poly_inv(result.space_dimension(), UNIVERSE);
    Linear_Expression lin_inv(0);
    */
    cout << endl
         << "* Propagated Invariant at " << name << endl
         << "  " << *invariant;
}

void Location::extract_invariant_for_initial_by_recursive_eliminating(
    Constraint_System const& pre_cs) {
    if ((int)(pre_cs.space_dimension()) == (n + 1)) {
        C_Polyhedron Result(pre_cs);
        solve_invariant_from_generator(Result.minimized_generators());
        return;
    }

    //    Here is the function of
    //    "extract_invariant_for_initial_by_recursive_eliminating()" It is
    //    similar to the code in 'Farkas' part.

    int i, j, nc, nd;
    nd = fd->get_dimension();
    Constraint_System::const_iterator vi;
    Generator_System::const_iterator vj;
    cout << endl
         << "In extract_invariant_for_initial_by_recursive_eliminating(), 「 "
         << name << ", l: " << l << ", n: " << n << ", nd: " << nd << " 」"
         << endl;
    cout << "- - Currently, the number of variables in Ax<=b is : "
         << pre_cs.space_dimension();
    // cout<<"- - - 1. Constraint_System cs is "<<endl<<"      "<<cs;

    //    For minimized
    C_Polyhedron ph(pre_cs);
    Constraint_System cs = ph.minimized_constraints();

    //    1.Count the number of multiplier variables(that is generator y)
    //    required
    nc = 0;
    for (vi = cs.begin(); vi != cs.end(); ++vi) {
        nc++;
    }
    C_Polyhedron result(
        nc, UNIVERSE);  // create a universe polyhedron of nc-dimensions
    Linear_Expression lin(0);

    //    2.Now build the constraints for y^T*A=0,
    //    here, 'A' only contains a set of coefficient of C in last location.
    for (i = 0; i < static_cast<int>(cs.space_dimension()); i++) {
        if (static_cast<int>(cs.space_dimension()) - (n + 1) <=
            i) {  // only select the coefficient about the last set of location
            lin = Linear_Expression(0);
            j = 0;
            for (vi = cs.begin(); vi != cs.end(); ++vi) {
                lin = lin - (*vi).coefficient(Variable(i)) * Variable(j);
                j++;
            }
            result.add_constraint(
                lin == 0);  // Add the constraint lin==0 to the result
        }
    }
    // cout<<endl<<"- - - 2. y^T*A=0 is "<<endl<<"      "<<result;

    //    3.Now add the constraints on the multipliers
    j = 0;
    for (vi = cs.begin(); vi != cs.end(); ++vi) {
        if ((*vi).type() == Constraint::NONSTRICT_INEQUALITY) {
            //  Set y>=0 if Ax <= b
            result.add_constraint(Variable(j) >= 0);
        } else if ((*vi).type() == Constraint::EQUALITY) {
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
    for (vi = test_cs.begin(); vi != test_cs.end(); ++vi) {
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
         << (n + 1);

    //    5.After we get y^T*A=0, then transfer from the generator of y^T to
    //    values of y^T
    // cout<<endl<<"- - - 5. y^T 's generators() is "<<endl<<"
    // "<<result1.generators(); cout<<endl<<"- - - 6. y^T 's
    // minimized_generators() is "<<endl<<" "<<result1.minimized_generators();
    Generator_System gs = result1.minimized_generators();
    C_Polyhedron result2(cs.space_dimension() - (n + 1),
                         UNIVERSE);  // Store y^T*b>=0
    for (vj = gs.begin(); vj != gs.end(); vj++) {
        Generator g = (*vj);
        vector<int> y(nc, -999);
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
        for (vi = cs.begin(); vi != cs.end(); ++vi) {
            for (i = 0; i < static_cast<int>(cs.space_dimension()); i++) {
                if (i < static_cast<int>(cs.space_dimension()) - (n + 1)) {
                    lin1 = lin1 + y[j] * (*vi).coefficient(Variable(l + i)) *
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
    for (vi = cs1.begin(); vi != cs1.end(); ++vi) {
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
    // add c_l=0
    for (int i = 0; i < n; i++)
        // trivial->add_constraint_and_minimize(Variable(l+i)==0);
        trivial->add_constraint(Variable(l + i) == 0);
    return;
}

void Location::add_to_trivial(C_Polyhedron& trivial) {
    // add c_l=0
    for (int i = 0; i < n; i++)
        // trivial.add_constraint_and_minimize(Variable(l+i)==0);
        trivial.add_constraint(Variable(l + i) == 0);
    return;
}

void Location::extract_invariants_and_update(C_Polyhedron& pp,
                                             C_Polyhedron& dualp) {
    cout << endl << "For location: " << name;
    cout << endl
         << "「 l: " << l << ", n: " << n << ", nd: " << fd->get_dimension()
         << " 」";
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
    int nd = fd->get_dimension();
    cout << endl << "For location: " << name;
    cout << endl << "「 l: " << l << ", n: " << n << ", nd: " << nd << " 」";
    // cout<<endl<<"C_Polyhedron & pp is "<<endl<<"    "<<pp;
    if (projection == "no_projection") {
        cout << endl << "Do not use projection";
        if (debug_2) {
            cout << endl << "------------------------------";
            cout << endl
                 << "- cpoly.constraints: " << endl
                 << "  " << pp.minimized_constraints();
            cout << endl
                 << "- cpoly.generators: " << endl
                 << "  " << pp.minimized_generators();
        }
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
    cout << endl << "= Doing Propagation at Location " << name;
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
    Generator_System::const_iterator vi = gs.begin();
    // cout<<endl<<"l: "<<l<<", n: "<<n<<endl;
    for (; vi != gs.end(); vi++) {
        // cout<<(*vi)<<endl;
        Generator g = *vi;
        // Extract coefficients from l to r of the generators and make a
        // constraint Add this constraint to the invariant polyhedron
        Linear_Expression lin;
        for (dimension_type i = g.space_dimension(); i-- > 0;) {
            lin += g.coefficient(Variable(i)) * Variable(i);
        }
        Linear_Expression lin1;
        int c;
        bool flag = true;
        for (int i = 0; i < n; i++) {
            if (!handle_integers(lin.coefficient(Variable(l + i)), c))
                flag = false;
            lin1 += c * Variable(i);
        }
        if (!handle_integers(lin.coefficient(Variable(l + n)), c))
            flag = false;
        lin1 += c;
        // cout<<name<<" => ";
        // print_lin_expression(cout,lin1,f);
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
    Constraint_System cs = ph.minimized_constraints();
    C_Polyhedron result(ph.space_dimension(), UNIVERSE);
    Linear_Expression lin2(0);
    Constraint_System::const_iterator vi2;
    // cout<<endl<<"n: "<<n;
    for (vi2 = cs.begin(); vi2 != cs.end(); vi2++) {
        lin2 = Linear_Expression(0);
        for (int i = 0; i < static_cast<int>(ph.space_dimension()); i++) {
            if (i < n) {
                lin2 = lin2 + (*vi2).coefficient(Variable(n + i)) * Variable(i);
            }
            if (n <= i) {
                lin2 = lin2 + (*vi2).coefficient(Variable(i - n)) * Variable(i);
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
    result.remove_higher_space_dimensions(n);
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
    Constraint_System cs = invariant->minimized_constraints();
    Constraint_System::const_iterator vi;
    C_Polyhedron* result;

    int i, j, nc, nd;

    // count the number of multiplier variables required
    nc = 0;
    for (vi = cs.begin(); vi != cs.end(); ++vi)
        nc++;

    nd = fd->get_dimension();

    result = new C_Polyhedron(
        nd + nc,
        UNIVERSE);  // create a universe polyhedron of nd +nc dimensions
    Linear_Expression lin(0);

    // Now build the constraints
    for (i = 0; i < n; i++) {
        lin = Linear_Expression(0);
        lin = lin - Variable(l + i);  // add -c_i to the constraint
        j = 0;
        for (vi = cs.begin(); vi != cs.end(); ++vi) {
            lin = lin + (*vi).coefficient(Variable(i)) * Variable(nd + j);
            j++;
        }
        result->add_constraint(lin ==
                               0);  // Add the constraint lin==0 to the result
    }

    // Now the constraints on the constant
    lin = Linear_Expression(0);
    lin = lin - Variable(l + n);  // add -d to the constraint
    j = 0;
    for (vi = cs.begin(); vi != cs.end(); ++vi) {
        lin = lin + (*vi).inhomogeneous_term() * Variable(nd + j);
        j++;
    }
    result->add_constraint(lin <= 0);

    // Now the constraints on the multipliers

    j = 0;
    for (vi = cs.begin(); vi != cs.end(); ++vi) {
        if ((*vi).type() == Constraint::NONSTRICT_INEQUALITY) {
            result->add_constraint(Variable(nd + j) >= 0);
        } else if ((*vi).type() == Constraint::STRICT_INEQUALITY) {
            cerr
                << "Location::compute_dual_constraints -- Warning: Encountered "
                   "Strict Inequality"
                << endl;
            cerr << "                " << (*vi) << endl;

            result->add_constraint(
                Variable(nd + j) >=
                0);  // Just handle it as any other inequality
        }
        j++;
    }
    // Now those are all the constraints.

    // contains_test(*result, nd);
    //  * * *
    //  Old method
    result->remove_higher_space_dimensions(
        nd);  // Remove the excess dimensions to obtain a new Polyhedron
    // * * *
    // * * *
    // New method
    // eliminate_by_Farkas(*result, nd);
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