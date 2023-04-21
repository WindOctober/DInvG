
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
 * Filename: ToolUtils.cc
 * Author: Hongming Liu<hm-liu@sjtu.edu.cn>
 * Comments: Some utilities for writing code.
 * Copyright: Please see README file.
 */

#ifndef __TOOLUTILS__H_
#define __TOOLUTILS__H_

#include <algorithm>
#include <iostream>
#include <vector>

#include "Macro.h"

using namespace std;

inline int length(int num)
{
    int sum = 0;

    if (num == 0) {
        sum = 1;
    }
    else {
        while (num) {
            sum++;
            num /= 10;
        }
    }
    return sum;
}

inline void autoprint(int max_index, int index)
{
    int diff = length(max_index) - length(index);
    for (int i = 1; i <= diff; i++) {
        cout << " ";
    }
    cout << index;
}

inline string& replace_all(string& src, const string& old_value,
                           const string& new_value)
{
    for (string::size_type pos(0); pos != string::npos;
         pos += new_value.length()) {
        if ((pos = src.find(old_value, pos)) != string::npos) {
            src.replace(pos, old_value.length(), new_value);
        }
        else
            break;
    }
    return src;
}

class DepthCounter {
   private:
    /*
     * pbc = prune bang count
     */
    vector<int> pbc_in_depth;

   public:
    void init_depth_size(int tree_size);
    void set_pbc_at_depth(int depth);
    int get_pbc_at_depth(int depth);
    void clearall();
};

class Counter {
   private:
    vector<DepthCounter> pre_pbc_at_location_in_depth;
    vector<DepthCounter> pst_pbc_at_location_in_depth;

   public:
    int get_location_size();
    void set_location_index_and_init_depth(int target_index, int tree_size);
    DepthCounter& get_location_pre_counter(int target_index);
    DepthCounter& get_location_pst_counter(int target_index);
    void set_pre_pbc_at_location_and_depth(int target_index, int depth);
    void set_pst_pbc_at_location_and_depth(int target_index, int depth);
    int get_pre_pbc_about_location_and_depth(int target_index, int depth);
    int get_pst_pbc_about_location_and_depth(int target_index, int depth);
};

#endif