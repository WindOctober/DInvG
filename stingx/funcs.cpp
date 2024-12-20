
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

#include "funcs.h"

int gcd(int a, int b) {
    a = std::abs(a);
    b = std::abs(b);
    while (b != 0) {
        int temp = b;
        b = a % b;
        a = temp;
    }

    return a;
}


long gcd(long a, long b) {
    if (a < 0)
        a = -a;

    if (b < 0)
        b = -b;

    while (b != 0) {
        long temp = b;
        b = a % b;
        a = temp;
    }

    return a;
}

int lcm(int a, int b) {
    if (a == 0 || b == 0)
        return 0;

    if (a < 0)
        a = -a;

    if (b < 0)
        b = -b;

    int gcd = a;

    while (gcd % b != 0)
        gcd += a;

    return gcd;
}


/*
WORD listify(int * t, int n){

   WORD out=NIL;
   int i;
   for (i=n-1;i>=0;i--)
      out=COMP(t[i],out);

   return out;
}

*/

string int_to_str(int i) {
    if (i == 0) {
        return string("0");
    }
    bool neg = false;
    string ret;
    if (i < 0) {
        i = -i;
        neg = true;
    }
    char c;
    while (i > 0) {
        c = '0' + (i % 10);
        ret = c + ret;
        i /= 10;
    }

    if (neg)
        ret = '-' + ret;

    return ret;
}
