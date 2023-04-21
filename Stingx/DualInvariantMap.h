
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
 * Filename: DualInvariantMap
 * Author: Sriram Sankaranarayanan<srirams@theory.stanford.edu>
 * Comments: Inactive module.. reimplemented as part of the DUCHESS effort.
 *           Code works but very bare-bones and included only because I am
 *           to lazy to remove it and fix the rest of the implementation.
 * Copyright: Please see README file.
 */

#ifndef LS__DUAL_INVARIANT_MAP__H_
#define LS__DUAL_INVARIANT_MAP__H_

#include <iostream>
#include <map>
#include <string>
#include <vector>

#include "Clump.h"
#include "Context.h"
#include "DualTransitionRelation.h"
#include "Expression.h"
#include "ExpressionStore.h"
#include "InvariantMap.h"
#include "LinTransform.h"
#include "Location.h"
#include "TransitionRelation.h"
#include "ppl.hh"
#include "var-info.h"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

class DualInvariantMap : public InvariantMap {
   protected:
    // f_ of the base class is used as a dual var_info
    // n_ of the base class is the number of dual variables

    void populate();

   public:
    DualInvariantMap(int n, var_info* fd, vector<Location*> const& vloc);

    // DualInvariantMaps can only be narrowed. Do not widen!!!!

    void H79_widening_assign(DualInvariantMap const& im)
    {
        // This should not be called in the first place
        cerr << "FATAL :: DualInvariantMap :: widening called" << endl;
        exit(1);
    }

    void BHRZ03_widening_assign(DualInvariantMap const& im)
    {
        // This should not be called in the first place
        cerr << "FATAL :: DualInvariantMap :: widening called" << endl;
        exit(1);
    }

    void H79_narrowing_assign(DualInvariantMap const& im);

    // I will implement this once I figure out what is so special about it :-)

    void Special_narrowing_assign(DualInvariantMap const& im);

    void primalize(InvariantMap& result);
};

#endif
