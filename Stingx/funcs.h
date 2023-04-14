
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
 * Filename: Expression
 * Author: Sriram Sankaranarayanan<srirams@theory.stanford.edu>
 * Comments: some misc. functions
 *
 * Copyright: Please see README file.
 */


#ifndef __FUNCS__H_
#define __FUNCS__H_


#include "Rational.h"
// Just some overall functions that I will need
#include <string>
using namespace std;

int gcd (int a, int b);

long gcd (long a, long b);

int lcm (int a, int b);

//Rational rationalize(RN & p);

string int_to_str(int i);

#endif
