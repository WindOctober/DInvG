
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

#include "SparseLinExpr.h"

#include <iostream>
#include <map>

#include "PolyUtils.h"
#include "funcs.h"
#include "myassertions.h"

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

void SparseLinExpr::clear_out() {
    map_ration.clear();  // that should erase all the entries!
}

void SparseLinExpr::initialize(int n, var_info* info) {
    varNum = n;
    varInfo = info;
    map_ration.clear();
    count_ = 1;
    info_set_ = true;
}

bool SparseLinExpr::_class_invariant_check() const {
    IRMap::const_iterator vi;
    if (map_ration.empty())
        return true;
    for (vi = map_ration.begin(); vi != map_ration.end(); ++vi) {
        if ((*vi).first < 0 || (*vi).first > varNum) {
            cerr << " Illegal Dimensions!" << endl;
            return false;
        }
        if ((*vi).second == 0) {
            cerr << "Zero Entry" << endl;
            return false;
        }
    }

    return true;
}

void SparseLinExpr::add_coefficient(int index, Rational const& what) {
    //
    // this will insert the index if it has not been introduced by
    // default The constructor Rational() will be called-- that
    // produces a Rational that is zero by default and then G.W. things
    // should work fine!
    //

    PRECONDITION((index >= 0 && index < varNum + 1),
                 "SparseLinExpr::add_coefficient --> illegal index");

    if (what == 0)
        return;

    Rational& r = map_ration[index];

    r += what;

    if (r == 0) {
        // remove the position
        map_ration.erase(index);
    }

    return;
}

void SparseLinExpr::subtract_coefficient(int index, Rational const& what) {
    //
    // this will insert the index if it has not been introduced by
    // default The constructor Rational() will be called-- that
    // produces a Rational that is zero by default and then G.W. things
    // should work fine!
    //

    PRECONDITION((index >= 0 && index < varNum + 1),
                 "SparseLinExpr::subtract_coefficient --> illegal index");

    if (what == 0)
        return;

    Rational& r = map_ration[index];

    r -= what;

    if (r == 0) {
        // remove the position
        map_ration.erase(index);
    }

    return;
}

void SparseLinExpr::subtract_scaled(SparseLinExpr const& x,
                                    Rational const& scale) {
    IRMap const& xm = x.get_map();
    IRMap::const_iterator vi;
    for (vi = xm.begin(); vi != xm.end(); ++vi) {
        subtract_coefficient((*vi).first, (*vi).second * scale);
    }
    return;
}

void SparseLinExpr::add_scaled(SparseLinExpr const& x, Rational const& scale) {
    IRMap const& xm = x.get_map();
    IRMap::const_iterator vi;
    for (vi = xm.begin(); vi != xm.end(); ++vi) {
        add_coefficient((*vi).first, (*vi).second * scale);
    }
    return;
}

void SparseLinExpr::setCoefficient(int index, Rational const& what) {
    //
    // this will insert the index if it has not been introduced by
    // default The constructor Rational() will be called-- that
    // produces a Rational that is zero by default and then G.W. things
    // should work fine!
    //

    PRECONDITION((index >= 0 && index < varNum + 1),
                 "SparseLinExpr::setCoefficient --> illegal index");

    Rational& r = map_ration[index];

    r = what;

    if (r == 0) {
        // remove the position
        map_ration.erase(index);
    }

    return;
}

//
// This is inline only for this particular file
//

inline Rational SparseLinExpr::get_coefficient(int index) const {
    PRECONDITION((index >= 0 && index < varNum + 1),
                 "SparseLinExpr::get_coefficient --> illegal index" << index);

    IRMap::const_iterator pos = map_ration.find(index);

    if (pos == map_ration.end())
        return Rational();

    return (*pos).second;
}

SparseLinExpr::SparseLinExpr() : varNum(0), count_(1), info_set_(false) {}

SparseLinExpr::SparseLinExpr(int n, var_info* info)
    : varNum(n), varInfo(info), count_(1), info_set_(true) {
    PRECONDITION(n <= varInfo->getDim(), " Not enough print info ");
}

SparseLinExpr::SparseLinExpr(LinExpr const& ll)
    : varNum(ll.getDim()),
      varInfo(ll.getInfo()),
      count_(ll.getCount()),
      info_set_(true) {
    int i;

    for (i = 0; i < varNum + 1; i++) {
        if (ll(i) != 0) {
            add_coefficient(i, ll(i));
        }
    }
}

SparseLinExpr SparseLinExpr::operator+(SparseLinExpr const& p1) const {
    //
    // I am adding this restriction ftb. If it proves to be a p.i.b then I will
    // remove it in later versions
    //

    PRECONDITION((p1.getDim() == varNum),
                 " SparseLinExpr::operator+ : trying to "
                 "add expressions of different size?");

    SparseLinExpr ret_val(varNum, varInfo);

    if (!is_printable())
        ret_val.make_unprintable();

    // for the time being, I will just iterate through all the elements in p1
    // and p2 and add them to ret_val

    Rational tmp;

    IRMap::const_iterator vi;

    for (vi = map_ration.begin(); vi != map_ration.end(); vi++) {
        ret_val.add_coefficient((*vi).first, (*vi).second);
    }

    IRMap const& mp = p1.get_map();

    IRMap::const_iterator vj;

    for (vj = mp.begin(); vj != mp.end(); vj++) {
        ret_val.add_coefficient((*vj).first, (*vj).second);
    }

    // ret_val.prune();

    return ret_val;
}

SparseLinExpr SparseLinExpr::operator-(SparseLinExpr const& p1) const {
    //
    // I am adding this restriction ftb. If it proves to be a p.i.b then I will
    // remove it in later versions
    //

    PRECONDITION((p1.getDim() == varNum),
                 " SparseLinExpr::operator+ : trying to "
                 "add expressions of different size?");

    SparseLinExpr ret_val(varNum, varInfo);

    if (!is_printable())
        ret_val.make_unprintable();

    // for the time being, I will just iterate through all the elements in p1
    // and p2 and add them to ret_val

    Rational tmp;

    IRMap::const_iterator vi;

    for (vi = map_ration.begin(); vi != map_ration.end(); vi++) {
        ret_val.add_coefficient((*vi).first, (*vi).second);
    }

    IRMap const& mp = p1.get_map();

    IRMap::const_iterator vj;

    for (vj = mp.begin(); vj != mp.end(); vj++) {
        ret_val.subtract_coefficient((*vj).first, (*vj).second);
    }

    // ret_val.prune();

    return ret_val;
}

SparseLinExpr& SparseLinExpr::operator+=(SparseLinExpr const& sl) {
    PRECONDITION(
        (sl.getDim() == varNum),
        "SparseLinExpr::operator+=  -- addition over incompatible dimensions");

    IRMap::const_iterator vj;
    IRMap const& mp = sl.get_map();

    for (vj = mp.begin(); vj != mp.end(); ++vj) {
        add_coefficient((*vj).first, (*vj).second);
    }
    return (*this);
}

SparseLinExpr& SparseLinExpr::operator-=(SparseLinExpr const& sl) {
    PRECONDITION(
        (sl.getDim() == varNum),
        "SparseLinExpr::operator-= subtraction over incompatible dimensions");

    IRMap::const_iterator vj;
    IRMap const& mp = sl.get_map();

    for (vj = mp.begin(); vj != mp.end(); ++vj) {
        subtract_coefficient((*vj).first, (*vj).second);
    }

    return (*this);
}

void SparseLinExpr::merge_assign(SparseLinExpr& ex2) {
    int n2 = ex2.getDim(), n1 = varNum;
    //
    // I am not creating a new var_info
    // any attempt to print this may not go well
    //

    varNum += n2;  // increase the dimensions!!

    IRMap const& m2 = ex2.get_map();
    IRMap::const_iterator vi;
    for (vi = m2.begin(); vi != m2.end(); vi++) {
        setCoefficient((*vi).first + n1, (*vi).second);
    }

    return;
}

SparseLinExpr& SparseLinExpr::operator=(SparseLinExpr const& p1) {
    initialize(p1.getDim(), p1.getInfo());

    count_ = p1.getCount();

    IRMap::const_iterator vi;
    IRMap const& mp = p1.get_map();

    for (vi = mp.begin(); vi != mp.end(); ++vi) {
        setCoefficient((*vi).first, (*vi).second);
    }

    return (*this);
}

SparseLinExpr& SparseLinExpr::operator*=(Rational const& r) {
    if (r == 0) {
        clear_out();
        return (*this);
    }

    IRMapIterator vi;

    for (vi = map_ration.begin(); vi != map_ration.end(); ++vi) {
        INVARIANT(((*vi).second != 0),
                  "Class SparseLinExpr -- Invariant violated");

        ((*vi).second) *= r;
    }

    return (*this);
}

SparseLinExpr& SparseLinExpr::operator*=(int i) {
    if (i == 0) {
        clear_out();
        return (*this);
    }
    IRMapIterator vi;

    for (vi = map_ration.begin(); vi != map_ration.end(); ++vi) {
        INVARIANT(((*vi).second != 0),
                  "Class SparseLinExpr -- Invariant violated");

        ((*vi).second) *= i;
    }

    return (*this);
}

bool SparseLinExpr::operator==(SparseLinExpr const& t) const {
    const IRMap& mp = t.get_map();

    return (map_ration == mp);  // That should do it?
}

Rational SparseLinExpr::operator()(int index) const {
    return get_coefficient(index);
}

bool SparseLinExpr::is_constant() const {
    INVARIANT((_class_invariant_check()),
              "Class SparseLinExpr:: Invariant violation");

    if (map_ration.size() == 0)
        return true;
    if (map_ration.size() > 1)
        return false;
    IRMap::const_iterator vt = map_ration.begin();

    // Is the only entry for the constant?
    if ((*vt).first == varNum)
        return true;

    return false;
}

int SparseLinExpr::getDenLcm() const {
    IRMap::const_iterator vi;
    IRPair pir;
    int run = 1;
    for (vi = map_ration.begin(); vi != map_ration.end(); ++vi) {
        pir = (*vi);
        INVARIANT((pir.second != 0),
                  " Class SparseLinExpr --> Invariant violated. Key "
                      << pir.first << " has zero entry ");

        run = lcm(run, (pir.second).den());
    }

    return run;
}

int SparseLinExpr::getNumGcd() const {
    int run = 1;
    bool first_number_seen = false;

    IRMap::const_iterator vi;
    IRPair pir;

    for (vi = map_ration.begin(); vi != map_ration.end(); ++vi) {
        pir = (*vi);
        INVARIANT((pir.second != 0),
                  " Class SparseLinExpr --> Invariant violated. Key "
                      << pir.first << " has zero entry ");
        if (!first_number_seen) {
            first_number_seen = true;
            run = (pir.second).num();
        } else
            run = gcd(run, (pir.second).num());
    }

    return run;
}

bool SparseLinExpr::equiv(SparseLinExpr const& l1, Rational& factor) const {
    // check if there is a factor such that factor * this = l1

    if (l1.isZero()) {
        factor = 0;
        return true;
    }

    // If l1 is zero and I am not, return false

    if (isZero())
        return false;

    // now check if for each entry in me, the corresponding entry in l1 behaves
    // OK

    IRMap const& mp = l1.get_map();
    IRMap::const_iterator vi, vj;
    // If sizes are not the same, then assuming the class invariant, there is
    // no way

    // as a lark, I will check the class invariant here

    INVARIANT((_class_invariant_check()),
              "Class SparseLinExpr:: Invariant violation");

    if (mp.size() != map_ration.size()) {
        factor = 0;
        return false;
    }

    // now find a factor and check for it
    vi = map_ration.begin();
    vj = mp.begin();
    if (vi->first != vj->first) {
        return false;
    }

    factor = ((*vi).second).inverse() * ((*vj).second);

    for (; vi != map_ration.end() && vj != mp.end(); ++vi, ++vj) {
        if ((vi->first != vj->first) ||
            ((factor * (*vi).second) != (*vj).second))
            return false;
    }

    return true;
}

void SparseLinExpr::print(ostream& out) const {
    PRECONDITION(info_set_,
                 " asked to print an Expression without a valid var-info ");

    INVARIANT((_class_invariant_check()),
              "Class SparseLinExpr:: Invariant violation");

    // print this stuff

    if (isZero()) {
        out << " 0 ";
        return;
    }
    if (is_constant()) {
        out << get_coefficient(varNum);
        return;
    }

    IRMap::const_iterator vi = map_ration.begin();

    out << (*vi).second << " * " << varInfo->getName((*vi).first);
    vi++;
    for (; vi != map_ration.end(); ++vi) {
        INVARIANT(((*vi).second != 0),
                  "Class SparseLinExpr ::print() --> Invariant violated");

        if (!((*vi).second < 0))
            out << " + ";

        if (vi->first < varNum)
            out << (*vi).second << " * " << varInfo->getName((*vi).first);
        else
            out << (*vi).second;
    }
}

Rational SparseLinExpr::evaluate(Generator const& g) const {
    IRMap::const_iterator vi;
    Rational rt(0, 1), c;
    int i, j;
    for (vi = map_ration.begin(); vi != map_ration.end(); ++vi) {
        i = (*vi).first;

        c = (*vi).second;

        if (i < varNum) {
            // If it is not the constant term, find its coefficient and
            // multiply with mine
            j = handleInt(g.coefficient(Variable(i)));
            c *= Rational(j, 1);
        }
        // add to the return value
        rt += c;
    }

    return rt;
}

ostream& operator<<(ostream& os, SparseLinExpr const& sp) {
    sp.print(os);
    return os;
}

SparseLinExpr operator*(Rational const& i, SparseLinExpr const& p1) {
    SparseLinExpr p(p1);
    p *= i;
    return p;
}

SparseLinExpr operator*(SparseLinExpr const& p1, Rational const& i) {
    SparseLinExpr p(p1);
    p *= i;
    return p;
}

SparseLinExpr operator*(int i, SparseLinExpr const& p1) {
    SparseLinExpr p(p1);
    p *= i;
    return p;
}

Linear_Expression SparseLinExpr::toLinExpression() const {
    int j = getDenLcm();
    int num, den;

    num = get_coefficient(varNum).num();
    den = get_coefficient(varNum).den();

    Linear_Expression l(num * j / den);  // set the constant term
    for (int i = 0; i < varNum; i++) {
        num = get_coefficient(i).num();
        den = get_coefficient(i).den();
        l = l + (num * j / den) * Variable(i);
    }
    return l;
}

Constraint SparseLinExpr::get_constraint(int ineqType) const {
    Linear_Expression l = toLinExpression();
    switch (ineqType) {
        case TYPE_LEQ:
            return l <= 0;
        case TYPE_EQ:
            return l == 0;
        case TYPE_GEQ:
            return l >= 0;
        case TYPE_GE:
            return l > 0;
        case TYPE_LE:
            return l < 0;
    }
    return l == 0;  // by default
}


SparseLinExpr operator*(SparseLinExpr const& p1, int i) {
    SparseLinExpr p(p1);
    p *= i;
    return p;
}

