
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
 * Filename: Elimination.cc
 * Author: Hongming Liu<hm-liu@sjtu.edu.cn>
 * Comments: Some projection methods for polyhedron.
 * Copyright: Please see README file.
 */


#ifndef __ELIMINATION__H_
#define __ELIMINATION__H_

#include <iostream>
#include "ppl.hh"
#include "PolyUtils.h"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

void repack_constraints_based_on_protection(Constraint_System & cs, Constraint_System & cs_only_unprotected, Constraint_System & cs_mixed_protected, Constraint_System & cs_only_protected, int l, int r);
void restruct_generators(Generator_System & gs);

void eliminate_by_Farkas(C_Polyhedron & result, int lb);
void Project_by_Farkas(C_Polyhedron & result, int l, int r);
void Project_by_Kohler(C_Polyhedron & result, int l, int r);
void Project_by_FouMot(C_Polyhedron & result, int l, int r);
void Project(C_Polyhedron & result, int l, int r);

void contains_test(C_Polyhedron & poly, int lb);

void bring_to_forward(C_Polyhedron & result, int l, int r);
C_Polyhedron const & swap2_index_and_divide_from(C_Polyhedron & ph, int index);
C_Polyhedron swap_index_and_divide_from(C_Polyhedron & ph, int index);

#endif