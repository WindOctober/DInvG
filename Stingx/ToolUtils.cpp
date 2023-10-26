
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

#include "ToolUtils.h"

/*
 * Class::DepthCounter
 */

void DepthCounter::init_depth_size(int tree_size) {
    int init_pbc_value = 0;
    for (int i = 0; i < tree_size; i++) {
        pbc_in_depth.push_back(init_pbc_value);
    }
}

void DepthCounter::set_pbc_at_depth(int depth) {
    pbc_in_depth[depth]++;
}

int DepthCounter::get_pbc_at_depth(int depth) {
    return pbc_in_depth[depth];
}

void DepthCounter::clearall() {
    vector<int>().swap(pbc_in_depth);
}

/*
 * Class::Counter
 */

int Counter::get_location_size() {
    if (pre_pbc_at_location_in_depth.size() ==
        pst_pbc_at_location_in_depth.size()) {
        return pre_pbc_at_location_in_depth.size();
    } else {
        cout << endl << "Error: pre_pbc_at_location_in_depth != pst";
        return -1;
    }
}

void Counter::set_location_index_and_init_depth(int curId,
                                                int tree_size) {
    int gap;
    if (get_location_size() != -1) {
        gap = curId - get_location_size();
    } else {
        cout << endl << "get_location_size() incurs Error!";
    }

    if (gap < 0) {
        pre_pbc_at_location_in_depth[curId].clearall();
        pst_pbc_at_location_in_depth[curId].clearall();
    } else if (gap == 0) {
        DepthCounter pre_pbc_in_depth;
        DepthCounter pst_pbc_in_depth;

        pre_pbc_at_location_in_depth.push_back(pre_pbc_in_depth);
        pst_pbc_at_location_in_depth.push_back(pst_pbc_in_depth);
    } else if (gap > 0) {
        DepthCounter pre_pbc_in_depth;
        DepthCounter pst_pbc_in_depth;
        for (int i = 0; i < gap + 1; i++) {
            pre_pbc_at_location_in_depth.push_back(pre_pbc_in_depth);
            pst_pbc_at_location_in_depth.push_back(pst_pbc_in_depth);
        }
    }

    get_location_pre_counter(curId).init_depth_size(tree_size);
    get_location_pst_counter(curId).init_depth_size(tree_size);
}

DepthCounter& Counter::get_location_pre_counter(int curId) {
    return pre_pbc_at_location_in_depth[curId];
}

DepthCounter& Counter::get_location_pst_counter(int curId) {
    return pst_pbc_at_location_in_depth[curId];
}

void Counter::set_pre_pbc_at_location_and_depth(int curId, int depth) {
    pre_pbc_at_location_in_depth[curId].set_pbc_at_depth(depth);
}

void Counter::set_pst_pbc_at_location_and_depth(int curId, int depth) {
    pst_pbc_at_location_in_depth[curId].set_pbc_at_depth(depth);
}

int Counter::get_pre_pbc_about_location_and_depth(int curId, int depth) {
    return get_location_pre_counter(curId).get_pbc_at_depth(depth);
}

int Counter::get_pst_pbc_about_location_and_depth(int curId, int depth) {
    return get_location_pst_counter(curId).get_pbc_at_depth(depth);
}
