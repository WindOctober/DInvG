
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

#include "Elimination.h"

#include "Macro.h"

extern string projection;

void repack_constraints_based_on_protection(
    Constraint_System& cs,
    Constraint_System& cs_only_unprotected,
    Constraint_System& cs_mixed_protected,
    Constraint_System& cs_only_protected,
    int l,
    int r) {
    // cout<<endl;
    cout << endl
         << "> > > In repack_constraints_based_on_protection(), doing...";
    // cout<<endl<<"      "<<"Before repacking, cs is ";
    // cout<<endl<<"      "<<cs;

    Constraint_System::const_iterator vi;
    int flag_unprotected = 0;
    int flag_protected = 0;
    for (vi = cs.begin(); vi != cs.end(); vi++) {
        for (int i = 0; i < cs.space_dimension(); i++) {
            if (i < l || r <= i) {
                if ((*vi).coefficient(Variable(i)) != 0) {
                    flag_unprotected = 1;
                }
            } else if (l <= i && i < r) {
                if ((*vi).coefficient(Variable(i)) != 0) {
                    flag_protected = 1;
                }
            }
        }
        if (flag_unprotected == 1 && flag_protected == 0) {
            cs_only_unprotected.insert(*vi);
            flag_unprotected = 0;
        } else if (flag_unprotected == 0 && flag_protected == 1) {
            cs_only_protected.insert(*vi);
            flag_protected = 0;
        } else if (flag_unprotected == 1 && flag_protected == 1) {
            cs_mixed_protected.insert(*vi);
            flag_unprotected = 0;
            flag_protected = 0;
        }
    }

    // cout<<endl<<"      "<<"After repacking, cs_only_unprotected is ";
    // cout<<endl<<"      "<<cs_only_unprotected;
    // cout<<endl<<"      "<<"After repacking, cs_mixed_protected is ";
    // cout<<endl<<"      "<<cs_mixed_protected;
    // cout<<endl<<"      "<<"After repacking, cs_only_protected is ";
    // cout<<endl<<"      "<<cs_only_protected;
    cout << endl
         << "< < < Out of repack_constraints_based_on_protection(), done!";
    return;
}

void restruct_generators(Generator_System& gs) {
    // cout<<endl;
    // cout<<endl<<"> > > In restruct_generators(), doing...";

    int line_count = 0, point_count = 0, ray_count = 0, generator_count = 0;
    Generator_System temp_gs;
    Generator_System::const_iterator vi;

    for (vi = gs.begin(); vi != gs.end(); vi++) {
        generator_count++;
        if ((*vi).is_point()) {
            point_count++;
            temp_gs.insert(*vi);
        }
        if ((*vi).is_ray()) {
            ray_count++;
            temp_gs.insert(*vi);
        }
        if ((*vi).is_line()) {
            line_count++;
            Linear_Expression e;
            for (dimension_type i = (*vi).space_dimension(); i-- > 0;) {
                e += (*vi).coefficient(Variable(i)) * Variable(i);
            }
            temp_gs.insert(ray(e));
            temp_gs.insert(ray(-e));
        }
    }
    gs = temp_gs;

    if (point_count + ray_count + line_count != generator_count) {
        cout << endl << "Warning! point + ray + line != generator";
    }
    // cout<<endl<<"      "<<point_count<<" of Point";
    // cout<<endl<<"      "<<ray_count<<" of Ray";
    // cout<<endl<<"      "<<line_count<<" of Line";
    // cout<<endl<<"      "<<generator_count<<" of Generator";
    // cout<<endl<<"< < < Out of restruct_generators(), done!";
}

void eliminate_by_Farkas(C_Polyhedron& result, int lb) {
    cout << endl;
    cout << endl << "> > > In eliminate_by_Farkas(), doing...";
    // cout<<"- - - 1. Constraint_System cs is "<<endl<<"      "<<cs;
    Constraint_System::const_iterator vi;
    Generator_System::const_iterator vj;
    long unsigned int i, j;
    int equality_count = 0, non_strict_inequality_count = 0;

    //    For minimized
    Constraint_System cs = result.minimized_constraints();
    // cout<<endl<<"input cs is : "<<endl<<cs<<endl;

    //    Count the number of multiplier variables(that is generator y) required
    dimension_type n_y = 0;
    for (vi = cs.begin(); vi != cs.end(); ++vi) {
        n_y++;
    }
    C_Polyhedron yTAeq0(
        n_y, UNIVERSE);  // create a universe polyhedron of n_y-dimensions
    Linear_Expression yTA(0);

    //    Now build the constraints for y^T*A=0
    for (i = 0; i < cs.space_dimension(); i++) {
        if (i >= lb) {  // select coefficient about lambda
            yTA = Linear_Expression(0);
            j = 0;
            for (vi = cs.begin(); vi != cs.end(); ++vi) {
                yTA = yTA - (*vi).coefficient(Variable(i)) * Variable(j);
                j++;
            }
            // cout<<endl<<"yTA == 0 is "<<endl<<yTA<<" == 0 "<<endl;
            yTAeq0.add_constraint(
                yTA == 0);  // Add the constraint lin==0 to the result
        }
    }
    // cout<<endl<<"- - - 2. y^T*A=0 is "<<endl<<yTAeq0<<endl;

    //    Now the constraints on the multipliers
    j = 0;
    for (vi = cs.begin(); vi != cs.end(); ++vi) {
        if ((*vi).type() == Constraint::NONSTRICT_INEQUALITY) {
            //  Set y>=0 if Ax <= b
            non_strict_inequality_count++;
            // cout<<endl<<"Constraint is Non-Strict inequality"<<endl;
            // cout<<endl<<"add constraints "<<Variable(j)<<" >= 0"<<endl;
            yTAeq0.add_constraint(Variable(j) >= 0);
        } else if ((*vi).type() == Constraint::STRICT_INEQUALITY) {
            // cout<<endl<<"Constraint is Strict inequality"<<endl;
        } else if ((*vi).type() == Constraint::EQUALITY) {
            //  Do nothing if Ax == b
            equality_count++;
            // cout<<endl<<"Constraint is Equality"<<endl;
        } else {
            // cout<<endl<<"Unknown Constraint !! "<<endl;
        }
        j++;
    }
    if (equality_count + non_strict_inequality_count != n_y) {
        cout << endl
             << "Warning! equality + non_strict_inequality != Rows(Lines) in "
                "b>=Ax";
    }
    //    Now those are all the constraints.
    // cout<<endl<<"- - - 3. y^T*A=0 (has added some y>=0) is
    // "<<endl<<yTAeq0<<endl; cout<<endl<<"- - - 4. y^T*A=0 's
    // minimized_constraints() is "<<endl<<" "<<yTAeq0.minimized_constraints();

    //    For minimized
    Constraint_System cs_yTAeq0 = yTAeq0.minimized_constraints();
    C_Polyhedron poly_yTAeq0(cs_yTAeq0);
    //    Test for cout
    dimension_type nc_yTAeq0 = 0;
    for (vi = cs_yTAeq0.begin(); vi != cs_yTAeq0.end(); ++vi) {
        nc_yTAeq0++;
    }
    // cout<<endl<<"* * * The number of variables to be eliminated in 'A':
    // "<<(nc);

    //    After we get y^T*A=0, then transfer from the generator of y^T to
    //    values of y^T
    // cout<<endl<<"- - - 5. y^T 's generators() is "<<endl<<"
    // "<<poly_yTAeq0.generators(); cout<<endl<<"- - - 6. y^T 's
    // minimized_generators() is "<<endl<<poly_yTAeq0.minimized_generators();
    Generator_System gs_yTAeq0 = poly_yTAeq0.minimized_generators();
    restruct_generators(gs_yTAeq0);
    C_Polyhedron yTbgeq0(lb, UNIVERSE);  // Store y^T*b>=0
    for (vj = gs_yTAeq0.begin(); vj != gs_yTAeq0.end(); vj++) {
        Generator g = (*vj);
        int y[n_y] = {-999};
        // cout<<endl<<"[ ";
        for (dimension_type i = 0; i < g.space_dimension(); i++) {
            handleInt(g.coefficient(Variable(i)), y[i]);
            // cout<<y[i]<<", ";
        }
        // cout<<"]";
        //     Now, y^T are extracted.

        //    Now build the constraints for y^T*b>=0
        Linear_Expression yTb(0);
        j = 0;
        for (vi = cs.begin(); vi != cs.end(); ++vi) {
            for (i = 0; i < lb; i++) {
                yTb = yTb + y[j] * (*vi).coefficient(Variable(i)) *
                                Variable(i);  // second l+i turn to i
            }
            j++;
        }
        // cout<<endl<<"yTb >= 0 is "<<endl<<yTb<<" >= 0 "<<endl;
        yTbgeq0.add_constraint(yTb >= 0);

        // cout<<endl<<"- - - 7. y^T*b>=0(added in the loop) is
        // "<<endl<<yTbgqe0<<endl;
        //     Now yTbgeq0 contains the constraints of b( coefficient of
        //     invariant)
    }
    // cout<<endl<<"- - - 8. y^T*b>=0 is "<<endl<<yTbgeq0<<endl;

    //    For minimized
    Constraint_System cs_yTbgeq0 = yTbgeq0.minimized_constraints();
    C_Polyhedron poly_yTbgeq0(cs_yTbgeq0);
    // cout<<endl<<"- - - 9. y^T*b>=0 's minimized_constraints is "<<endl<<"
    // "<<poly_yTbgeq0;

    //    Test for cout
    dimension_type nc_yTbgeq0 = 0;
    for (vi = cs_yTbgeq0.begin(); vi != cs_yTbgeq0.end(); ++vi) {
        nc_yTbgeq0++;
    }
    // cout<<endl<<"- - - 10. y^T*b>=0 's minimized_generators is "<<endl<<"
    // "<<poly_yTbgeq0.minimized_generators()<<endl;

    result = poly_yTbgeq0;

    cout << endl
         << "- - - "
         << " { " << n_y << " } "
         << " * "
         << " [ " << lb << " ] "
         << " & "
         << " ' " << cs.space_dimension() - lb << " ' ";
    cout << " of Rows * Columns( [Vars] & 'to be eliminated' ) in [b] >= 'Ax'";
    cout << endl
         << "      "
         << "+{ " << equality_count << " } "
         << " of equalities";
    cout << endl
         << "      "
         << "+{ " << non_strict_inequality_count << " } "
         << " of non_strict-inequalities";
    cout << endl
         << "- - - "
         << "   " << nc_yTAeq0 << "   "
         << " * "
         << " { " << cs_yTAeq0.space_dimension() << " } "
         << " of Rows * Columns in {y^T} * 'A' == 0";
    cout << endl
         << "- - - "
         << "   " << nc_yTbgeq0 << "   "
         << " * "
         << " [ " << cs_yTbgeq0.space_dimension() << " ] "
         << " of Rows * Columns in {y^T} * [b] >= 0";
    cout << endl << "< < < Out of eliminate_by_Farkas(), done!";
    return;
}

void Project_by_Farkas(C_Polyhedron& result, int l, int r) {
    // cout<<endl;
    cout << endl << "> > > Project_by_Farkas(), doing...";
    // cout<<"- - - 1. Constraint_System cs is "<<endl<<"      "<<cs;
    Constraint_System::const_iterator vi;
    Generator_System::const_iterator vj;
    long unsigned int i, j;
    int equality_count = 0, non_strict_inequality_count = 0;

    //    For minimized
    Constraint_System cs = result.minimized_constraints();
    // cout<<endl<<"input cs is : "<<endl<<cs<<endl;

    //    Count the number of multiplier variables(that is generator y) required
    dimension_type n_y = 0;
    for (vi = cs.begin(); vi != cs.end(); ++vi) {
        n_y++;
    }
    C_Polyhedron yTAeq0(
        n_y, UNIVERSE);  // create a universe polyhedron of n_y-dimensions
    Linear_Expression yTA(0);

    //    Now build the constraints for y^T*A=0
    for (i = 0; i < cs.space_dimension(); i++) {
        if (i < l || i >= r) {  // select coefficient about lambda
            yTA = Linear_Expression(0);
            j = 0;
            for (vi = cs.begin(); vi != cs.end(); ++vi) {
                yTA = yTA - (*vi).coefficient(Variable(i)) * Variable(j);
                j++;
            }
            // cout<<endl<<"yTA == 0 is "<<endl<<yTA<<" == 0 "<<endl;
            yTAeq0.add_constraint(
                yTA == 0);  // Add the constraint lin==0 to the result
        }
    }
    // cout<<endl<<"- - - 2. y^T*A=0 is "<<endl<<yTAeq0<<endl;

    //    Now the constraints on the multipliers
    j = 0;
    for (vi = cs.begin(); vi != cs.end(); ++vi) {
        if ((*vi).type() == Constraint::NONSTRICT_INEQUALITY) {
            //  Set y>=0 if Ax <= b
            non_strict_inequality_count++;
            // cout<<endl<<"Constraint is Non-Strict inequality"<<endl;
            // cout<<endl<<"add constraints "<<Variable(j)<<" >= 0"<<endl;
            yTAeq0.add_constraint(Variable(j) >= 0);
        } else if ((*vi).type() == Constraint::STRICT_INEQUALITY) {
            // cout<<endl<<"Constraint is Strict inequality"<<endl;
        } else if ((*vi).type() == Constraint::EQUALITY) {
            //  Do nothing if Ax == b
            equality_count++;
            // cout<<endl<<"Constraint is Equality"<<endl;
        } else {
            // cout<<endl<<"Unknown Constraint !! "<<endl;
        }
        j++;
    }
    if (equality_count + non_strict_inequality_count != n_y) {
        cout << endl
             << "Warning! equality + non_strict_inequality != Rows(Lines) in "
                "b>=Ax";
    }
    //    Now those are all the constraints.
    // cout<<endl<<"- - - 3. y^T*A=0 (has added some y>=0) is
    // "<<endl<<yTAeq0<<endl; cout<<endl<<"- - - 4. y^T*A=0 's
    // minimized_constraints() is "<<endl<<" "<<yTAeq0.minimized_constraints();

    //    For minimized
    Constraint_System cs_yTAeq0 = yTAeq0.minimized_constraints();
    C_Polyhedron poly_yTAeq0(cs_yTAeq0);
    //    Test for cout
    dimension_type nc_yTAeq0 = 0;
    for (vi = cs_yTAeq0.begin(); vi != cs_yTAeq0.end(); ++vi) {
        nc_yTAeq0++;
    }
    // cout<<endl<<"* * * The number of variables to be eliminated in 'A':
    // "<<(nc);

    //    After we get y^T*A=0, then transfer from the generator of y^T to
    //    values of y^T
    // cout<<endl<<"- - - 5. y^T 's generators() is "<<endl<<"
    // "<<poly_yTAeq0.generators(); cout<<endl<<"- - - 6. y^T 's
    // minimized_generators() is "<<endl<<poly_yTAeq0.minimized_generators();
    Generator_System gs_yTAeq0 = poly_yTAeq0.minimized_generators();
    restruct_generators(gs_yTAeq0);
    C_Polyhedron yTbgeq0(r - l, UNIVERSE);  // Store y^T*b>=0
    for (vj = gs_yTAeq0.begin(); vj != gs_yTAeq0.end(); vj++) {
        Generator g = (*vj);
        int y[n_y] = {-999};
        // cout<<endl<<"[ ";
        for (dimension_type i = 0; i < g.space_dimension(); i++) {
            handleInt(g.coefficient(Variable(i)), y[i]);
            // cout<<y[i]<<", ";
        }
        // cout<<"]";
        //     Now, y^T are extracted.

        //    Now build the constraints for y^T*b>=0
        Linear_Expression yTb(0);
        j = 0;
        for (vi = cs.begin(); vi != cs.end(); ++vi) {
            for (i = l; i < r; i++) {
                yTb = yTb + y[j] * (*vi).coefficient(Variable(i)) *
                                Variable(i - l);  // second l+i turn to i
            }
            j++;
        }
        // cout<<endl<<"yTb >= 0 is "<<endl<<yTb<<" >= 0 "<<endl;
        yTbgeq0.add_constraint(yTb >= 0);

        // cout<<endl<<"- - - 7. y^T*b>=0(added in the loop) is
        // "<<endl<<yTbgqe0<<endl;
        //     Now yTbgeq0 contains the constraints of b( coefficient of
        //     invariant)
    }
    // cout<<endl<<"- - - 8. y^T*b>=0 is "<<endl<<yTbgeq0<<endl;

    //    For minimized
    Constraint_System cs_yTbgeq0 = yTbgeq0.minimized_constraints();
    C_Polyhedron poly_yTbgeq0(cs_yTbgeq0);
    // cout<<endl<<"- - - 9. y^T*b>=0 's minimized_constraints is "<<endl<<"
    // "<<poly_yTbgeq0;

    //    Test for cout
    dimension_type nc_yTbgeq0 = 0;
    for (vi = cs_yTbgeq0.begin(); vi != cs_yTbgeq0.end(); ++vi) {
        nc_yTbgeq0++;
    }
    // cout<<endl<<"- - - 10. y^T*b>=0 's minimized_generators is "<<endl<<"
    // "<<poly_yTbgeq0.minimized_generators()<<endl;

    result = poly_yTbgeq0;

    cout << endl
         << "- - - "
         << " { " << n_y << " } "
         << " * "
         << " [ " << r - l << " ] "
         << " & "
         << " ' " << cs.space_dimension() - (r - l) << " ' ";
    cout << " of Rows * Columns( [Vars] & 'to be eliminated' ) in [b] >= 'Ax'";
    cout << endl
         << "      "
         << "+{ " << equality_count << " } "
         << " of equalities";
    cout << endl
         << "      "
         << "+{ " << non_strict_inequality_count << " } "
         << " of non_strict-inequalities";
    cout << endl
         << "- - - "
         << "   " << nc_yTAeq0 << "   "
         << " * "
         << " { " << cs_yTAeq0.space_dimension() << " } "
         << " of Rows * Columns in {y^T} * 'A' == 0";
    cout << endl
         << "- - - "
         << "   " << nc_yTbgeq0 << "   "
         << " * "
         << " [ " << cs_yTbgeq0.space_dimension() << " ] "
         << " of Rows * Columns in {y^T} * [b] >= 0";
    cout << endl << "< < < Project_by_Farkas(), done!";
    return;
}

void Project_by_Kohler(C_Polyhedron& result, int l, int r) {
    cout << endl << "> > > Project_by_Kohler(), doing...";
    Constraint_System::const_iterator vi;
    Generator_System::const_iterator vj;
    long unsigned int i, j;
    int equality_count = 0, non_strict_inequality_count = 0;
    Constraint_System cs = result.minimized_constraints();
    Constraint_System cs_only_unprotected;
    Constraint_System cs_mixed_protected;
    Constraint_System cs_only_protected;

    int flag_unprotected = 0;
    int flag_protected = 0;
    for (vi = cs.begin(); vi != cs.end(); vi++) {
        for (int i = 0; i < cs.space_dimension(); i++) {
            if (i < l || r <= i) {
                if ((*vi).coefficient(Variable(i)) != 0) {
                    flag_unprotected = 1;
                }
            } else if (l <= i && i < r) {
                if ((*vi).coefficient(Variable(i)) != 0) {
                    flag_protected = 1;
                }
            }
        }
        if (flag_unprotected == 1 && flag_protected == 0) {
            cs_only_unprotected.insert(*vi);
            flag_unprotected = 0;
        } else if (flag_unprotected == 0 && flag_protected == 1) {
            cs_only_protected.insert(*vi);
            flag_protected = 0;
        } else if (flag_unprotected == 1 && flag_protected == 1) {
            cs_mixed_protected.insert(*vi);
            flag_unprotected = 0;
            flag_protected = 0;
        }
    }

    dimension_type n_y = 0;
    dimension_type n_y_only_unprotected = 0;
    dimension_type n_y_mixed_protected = 0;
    dimension_type n_y_only_protected = 0;
    for (vi = cs.begin(); vi != cs.end(); ++vi)
        n_y++;
    for (vi = cs_only_unprotected.begin(); vi != cs_only_unprotected.end();
         ++vi)
        n_y_only_unprotected++;
    for (vi = cs_mixed_protected.begin(); vi != cs_mixed_protected.end(); ++vi)
        n_y_mixed_protected++;
    for (vi = cs_only_protected.begin(); vi != cs_only_protected.end(); ++vi)
        n_y_only_protected++;
    C_Polyhedron yTAeq0(n_y_mixed_protected + n_y_only_unprotected, UNIVERSE);
    Linear_Expression yTA(0);

    //    Now build the constraints for y^T*A=0
    for (i = 0; i < cs.space_dimension(); i++) {
        if (i < l || r <= i) {  // select coefficient about lambda
            yTA = Linear_Expression(0);
            j = 0;
            for (vi = cs_mixed_protected.begin();
                 vi != cs_mixed_protected.end(); ++vi) {
                yTA = yTA - (*vi).coefficient(Variable(i)) * Variable(j);
                j++;
            }
            for (vi = cs_only_unprotected.begin();
                 vi != cs_only_unprotected.end(); ++vi) {
                yTA = yTA - (*vi).coefficient(Variable(i)) * Variable(j);
                j++;
            }
            // cout<<endl<<"yTA == 0 is "<<endl<<yTA<<" == 0 "<<endl;
            yTAeq0.add_constraint(
                yTA == 0);  // Add the constraint lin==0 to the result
        }
    }
    // cout<<endl<<"- - - 2. y^T*A=0 is "<<endl<<yTAeq0<<endl;

    //    Now the constraints on the multipliers
    j = 0;
    for (vi = cs_mixed_protected.begin(); vi != cs_mixed_protected.end();
         ++vi) {
        if ((*vi).type() == Constraint::NONSTRICT_INEQUALITY) {
            //  Set y>=0 if Ax <= b
            non_strict_inequality_count++;
            // cout<<endl<<"Constraint is Non-Strict inequality"<<endl;
            // cout<<endl<<"add constraints "<<Variable(j)<<" >= 0"<<endl;
            yTAeq0.add_constraint(Variable(j) >= 0);
        } else if ((*vi).type() == Constraint::STRICT_INEQUALITY) {
            // cout<<endl<<"Constraint is Strict inequality"<<endl;
        } else if ((*vi).type() == Constraint::EQUALITY) {
            //  Do nothing if Ax == b
            equality_count++;
            // cout<<endl<<"Constraint is Equality"<<endl;
        } else {
            // cout<<endl<<"Unknown Constraint !! "<<endl;
        }
        j++;
    }
    for (vi = cs_only_unprotected.begin(); vi != cs_only_unprotected.end();
         ++vi) {
        if ((*vi).type() == Constraint::NONSTRICT_INEQUALITY) {
            //  Set y>=0 if Ax <= b
            non_strict_inequality_count++;
            // cout<<endl<<"Constraint is Non-Strict inequality"<<endl;
            // cout<<endl<<"add constraints "<<Variable(j)<<" >= 0"<<endl;
            yTAeq0.add_constraint(Variable(j) >= 0);
        } else if ((*vi).type() == Constraint::STRICT_INEQUALITY) {
            // cout<<endl<<"Constraint is Strict inequality"<<endl;
        } else if ((*vi).type() == Constraint::EQUALITY) {
            //  Do nothing if Ax == b
            equality_count++;
            // cout<<endl<<"Constraint is Equality"<<endl;
        } else {
            // cout<<endl<<"Unknown Constraint !! "<<endl;
        }
        j++;
    }
    if (equality_count + non_strict_inequality_count !=
        n_y_mixed_protected + n_y_only_unprotected) {
        cout << endl
             << "Warning! equality + non_strict_inequality != Rows(Lines) in "
                "b>=Ax";
    }
    yTAeq0.remove_higher_space_dimensions(n_y_mixed_protected);
    Generator_System gs_yTAeq0 = yTAeq0.minimized_generators();
    restruct_generators(gs_yTAeq0);
    C_Polyhedron yTbgeq0(r - l, UNIVERSE);  // Store y^T*b>=0
    for (vj = gs_yTAeq0.begin(); vj != gs_yTAeq0.end(); vj++) {
        Generator g = (*vj);
        int y[n_y_mixed_protected] = {-999};
        for (dimension_type i = 0; i < g.space_dimension(); i++) {
            handleInt(g.coefficient(Variable(i)), y[i]);
        }
        Linear_Expression yTb(0);
        j = 0;
        for (vi = cs_mixed_protected.begin(); vi != cs_mixed_protected.end();
             ++vi) {
            if (y[j] != 0) {
                for (i = l; i < r; i++) {
                    yTb = yTb + y[j] * (*vi).coefficient(Variable(i)) *
                                    Variable(i - l);  // second l+i turn to i
                }
            }
            j++;
        }
        yTbgeq0.add_constraint(yTb >= 0);
    }
    Constraint_System cs_only_protected_corresponding_dimensions;
    Linear_Expression b_only_protected(0);
    for (vi = cs_only_protected.begin(); vi != cs_only_protected.end(); vi++) {
        j = 0;
        b_only_protected = Linear_Expression(0);
        for (i = l; i < r; i++) {
            b_only_protected =
                b_only_protected + (*vi).coefficient(Variable(i)) * Variable(j);
            j++;
        }
        if ((*vi).type() == Constraint::NONSTRICT_INEQUALITY) {
            cs_only_protected_corresponding_dimensions.insert(
                b_only_protected >= 0);
        } else if ((*vi).type() == Constraint::EQUALITY) {
            cs_only_protected_corresponding_dimensions.insert(
                b_only_protected == 0);
        }
    }
    yTbgeq0.add_constraints(cs_only_protected_corresponding_dimensions);
    result = yTbgeq0;
    cout << endl << "< < < Project_by_Kohler(), done!";
    return;
}

void Project_by_FouMot(C_Polyhedron& result, int l, int r) {
    cout << endl << "> > > Project_by_FouMot(), doing...";
    bring_to_forward(result, l, r);
    result.remove_higher_space_dimensions(r - l);
    cout << endl << "< < < Project_by_FouMot(), done!";
}

void Project(C_Polyhedron& result, int l, int r) {
    if (projection == "kohler_improvement_eliminate_c") {
        Project_by_Kohler(result, l, r);
    } else if (projection == "farkas_eliminate_c") {
        Project_by_Farkas(result, l, r);
    } else if (projection == "foumot_eliminate_c") {
        Project_by_FouMot(result, l, r);
    } else {
        cout << endl << "Wrong Type: " << projection << endl;
    }
}

void contains_test(C_Polyhedron& poly, int lb) {
    cout << endl;
    cout << endl << "> > > In contains_test(), doing...";

    C_Polyhedron poly_removed = poly;
    C_Polyhedron poly_Farkas = poly;
    poly_removed.remove_higher_space_dimensions(lb);
    eliminate_by_Farkas(poly_Farkas, lb);

    if (poly_removed.contains(poly_Farkas) &&
        poly_Farkas.contains(poly_removed)) {
        // Do nothing
    } else {
        cout << endl << "Warning! poly_removed != poly_Farkas";
    }

    cout << endl << "< < < Out of contains_test(), done!";
}

void bring_to_forward(C_Polyhedron& result, int l, int r) {
    C_Polyhedron ph(result.space_dimension(), UNIVERSE);
    Constraint_System cs = result.minimized_constraints();
    Linear_Expression lin(0);
    Constraint_System::const_iterator vi;
    for (vi = cs.begin(); vi != cs.end(); vi++) {
        lin = Linear_Expression(0);
        int flag = 0;
        for (int i = 0; i < ph.space_dimension(); i++) {
            if (i < r - l) {
                lin = lin + (*vi).coefficient(Variable(l + i)) * Variable(i);
            }
            if (r - l <= i) {
                if (flag < l) {
                    lin = lin + (*vi).coefficient(Variable(flag)) * Variable(i);
                    flag++;
                } else {
                    lin = lin + (*vi).coefficient(Variable(i)) * Variable(i);
                }
            }
        }
        lin = lin + (*vi).inhomogeneous_term();
        if ((*vi).type() == Constraint::NONSTRICT_INEQUALITY) {
            ph.add_constraint(lin >= 0);
        }
        if ((*vi).type() == Constraint::EQUALITY) {
            ph.add_constraint(lin == 0);
        }
    }
    result = ph;
}

C_Polyhedron const& swap2_index_and_divide_from(C_Polyhedron& ph, int index) {
    // cout<<endl<<"In swap2, before swap"<<endl<<ph;

    C_Polyhedron* result = new C_Polyhedron(ph.space_dimension(), UNIVERSE);
    // C_Polyhedron result(ph.space_dimension(), UNIVERSE);
    Constraint_System cs = ph.minimized_constraints();
    // cout<<endl<<"cs: "<<endl<<cs;
    Linear_Expression lin(0);
    Constraint_System::const_iterator vi;
    cout << endl << "index: " << index;
    for (vi = cs.begin(); vi != cs.end(); vi++) {
        lin = Linear_Expression(0);
        for (int i = 0; i < ph.space_dimension(); i++) {
            if (i < index) {
                lin =
                    lin + (*vi).coefficient(Variable(index + i)) * Variable(i);
            }
            if (index <= i) {
                lin =
                    lin + (*vi).coefficient(Variable(i - index)) * Variable(i);
            }
        }
        lin = lin + (*vi).inhomogeneous_term();
        // cout<<endl<<"lin: "<<lin;
        // cout<<endl<<"In swap, among swap"<<endl<<*result;
        if ((*vi).type() == Constraint::NONSTRICT_INEQUALITY) {
            result->add_constraint(lin >= 0);
            // cout<<endl<<"In swap, after among swap1"<<endl<<*result;
        }
        if ((*vi).type() == Constraint::EQUALITY) {
            result->add_constraint(lin == 0);
            // cout<<endl<<"In swap, after among swap2"<<endl<<*result;
        }
        // cout<<endl<<"In swap, after among swap3"<<endl<<*result;
    }
    // cout<<endl<<"In swap, after swap"<<endl<<*result;
    return *result;
}

C_Polyhedron swap_index_and_divide_from(C_Polyhedron& ph, int index) {
    // cout<<endl<<"In swap1, before swap"<<endl<<ph;

    C_Polyhedron result(ph.space_dimension(), UNIVERSE);
    Constraint_System cs = ph.minimized_constraints();
    // cout<<endl<<"cs: "<<endl<<cs;
    Linear_Expression lin(0);
    Constraint_System::const_iterator vi;
    for (vi = cs.begin(); vi != cs.end(); vi++) {
        lin = Linear_Expression(0);
        for (int i = 0; i < ph.space_dimension(); i++) {
            if (i < index) {
                lin =
                    lin + (*vi).coefficient(Variable(index + i)) * Variable(i);
            }
            if (index <= i) {
                lin =
                    lin + (*vi).coefficient(Variable(i - index)) * Variable(i);
            }
        }
        lin = lin + (*vi).inhomogeneous_term();
        // cout<<endl<<"lin: "<<lin;
        // cout<<endl<<"In swap, among swap"<<endl<<result;
        if ((*vi).type() == Constraint::NONSTRICT_INEQUALITY) {
            // cout<<endl<<"lin1: "<<lin;
            result.add_constraint(lin >= 0);
            // cout<<endl<<"In swap, after among swap1"<<endl<<result;
        }
        if ((*vi).type() == Constraint::EQUALITY) {
            // cout<<endl<<"lin2: "<<lin;
            result.add_constraint(lin == 0);
            // cout<<endl<<"In swap, after among swap2"<<endl<<result;
        }
        // cout<<endl<<"In swap, after among swap3"<<endl<<result;
    }
    // cout<<endl<<"In swap, after swap"<<endl<<result;
    return result;
}