
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

/*
 * filename: PolyUtils
 * Author: Sriram Sankaranarayanan < srirams@theory.stanford.edu>
 * Comments: Some utilities for handling polyhedra
 * Copyright: see README file for copyright information
 */

#ifndef __POLYUTILS__H_
#define __POLYUTILS__H_

#include <LinExpr.h>

#include <iostream>

#include "Clump.h"
#include "ppl.hh"
#include "var-info.h"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

ostream& print_polyhedron(ostream& in,
                          C_Polyhedron const& np,
                          const var_info* info);
// print only poly without prefix-symbol
void print_pure_polyhedron(C_Polyhedron const& np, const var_info* info);
// print only poly without prefix-symbol for array-invariants
void print_pure_polyhedron_for_arrayinv(C_Polyhedron const& np,
                                        const var_info* info);
// print only poly without prefix-symbol in cout instead of cout
void nt_print_pure_polyhedron(C_Polyhedron const& np, const var_info* info);
ostream& print_clump(ostream& in, Clump const& cl, const var_info* info);
void nt_print_pure_clump(Clump const& cl, const var_info* info);
ostream& print_lin_expression(ostream& in,
                              Linear_Expression const& lp,
                              const var_info* info);
void print_pure_lin_expression(Linear_Expression const& lp, const var_info* info);
ostream& print_constraint(ostream& in, Constraint const& cc, var_info* info);

void print_generators(ostream& out, Generator_System const& gg, var_info* info);
int handle_integers(Coefficient const& t);
bool handle_integers(Coefficient const& t, int& result);
C_Polyhedron* add_dimensions_initial(
    C_Polyhedron* p,
    int what);  // add what dimensions to p at the beginning
void dualize(C_Polyhedron const& what, C_Polyhedron& result);
void primal(C_Polyhedron const& what, C_Polyhedron& result);
void set_up_affine_transform(int n,
                             Constraint const& cc,
                             Linear_Expression& left,
                             Linear_Expression& right);
void test_and_add_generator(int n,
                            Generator const& a,
                            C_Polyhedron const& test,
                            C_Polyhedron& result);
// result is assumed to be narrower than what

void H79_narrow(C_Polyhedron& result, C_Polyhedron const& what);
void H79_narrow(C_Polyhedron& result,
                C_Polyhedron const& what,
                vector<Generator>& frames);

#endif
