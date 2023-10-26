
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

// #include <saclib.h>
#include "LinExpr.h"

#include <iostream>

#include "Macro.h"
#include "PolyUtils.h"
#include "Rational.h"
#include "funcs.h"
#include "myassertions.h"
#include "var-info.h"
using namespace std;

void LinExpr::initialize(int n, var_info* info) {
    // initialize
    this->n = n;
    this->info = info;
    lin.resize(n + 1, Rational(0, 0));
    count = 1;
    return;
}

void LinExpr::clear_out() {
    for (int i = 0; i < n + 1; ++i)
        lin[i] = 0;
}

LinExpr::LinExpr(LinExpr const& ll) {
    initialize(ll.getDim(), ll.getInfo());
    for (int i = 0; i < n + 1; i++)
        lin[i] = ll(i);
    return;
}

bool LinExpr::isZero() const {
    for (int i = 0; i < n + 1; i++) {
        if (lin[i] != 0)
            return false;
    }
    return true;
}

bool LinExpr::is_constant() const {
    for (int i = 0; i < n; i++) {
        if (lin[i] != 0)
            return false;
    }
    return true;
}

LinExpr::~LinExpr() {
    // nothing to do here.. thanks to the array -> vector conversion
    // STL rules!
}

LinExpr::LinExpr() {
    // default constructor overloaded.
    n = 0;
}

LinExpr::LinExpr(int n, var_info* info) {
    initialize(n, info);
}

void LinExpr::init_set(int n, var_info* info) {
    initialize(n, info);
}

inline Rational& LinExpr::operator[](int i) {
    return lin[i];
}

Rational LinExpr::operator()(int i) const {
    return lin[i];
}

LinExpr LinExpr::operator+(LinExpr const& p1) const {
    LinExpr tmp(n, info);
    for (int i = 0; i < n + 1; i++)
        tmp[i] = lin[i] + p1(i);
    return tmp;  // A reference to tmp.lin will be copied.. so this is not all
                 // that costly
}

LinExpr& LinExpr::operator+=(LinExpr const& p1) {
    for (int i = 0; i < n + 1; i++)
        lin[i] += p1(i);

    return *(this);
}

LinExpr LinExpr::operator-(LinExpr const& p1) const {
    LinExpr tmp(n, info);
    for (int i = 0; i < n + 1; i++)
        tmp[i] = lin[i] - p1(i);
    return tmp;  // A reference to tmp.lin will be copied.. so this is not all
                 // that costly
}

LinExpr& LinExpr::operator-=(LinExpr const& p1) {
    for (int i = 0; i < n + 1; i++)
        lin[i] -= p1(i);

    return *(this);
}

bool LinExpr::operator==(LinExpr const& p1) const {
    // note this is an equivalence check.
    Rational factor;
    bool ret = equiv(p1, factor);
    return ret && (factor != 0);
}

LinExpr& LinExpr::operator=(LinExpr const& p1) {
    // erase lin
    lin.erase(lin.begin(), lin.end());
    // reset
    initialize(p1.getDim(), p1.getInfo());  // reinitialize
    // assign
    for (int i = 0; i < n + 1; i++)
        lin[i] = p1(i);
    // return
    return *this;
}

LinExpr operator*(int j, LinExpr const& p1) {
    int n = p1.getDim();
    var_info* info = p1.getInfo();
    LinExpr tmp(n, info);
    for (int i = 0; i < n + 1; i++)
        tmp[i] = p1(i) * j;
    return tmp;  // A reference to tmp.lin will be copied.. so this is not all
                 // that costly
}

LinExpr operator*(LinExpr const& p1, Rational const& i) {
    int n = p1.getDim();
    var_info* info = p1.getInfo();
    LinExpr tmp(n, info);
    for (int j = 0; j < n + 1; j++)
        tmp[j] = i * p1(j);
    return tmp;  // A reference to tmp.lin will be copied.. so this is not all
                 // that costly
}

LinExpr operator*(Rational const& i, LinExpr const& p1) {
    int n = p1.getDim();
    var_info* info = p1.getInfo();
    LinExpr tmp(n, info);
    for (int j = 0; j < n + 1; j++)
        tmp[j] = i * p1(j);
    return tmp;
}

LinExpr& LinExpr::operator*=(Rational const& j) {
    for (int i = 0; i < n + 1; i++)
        lin[i] *= j;
    return *this;
}

LinExpr& LinExpr::operator*=(int j) {
    Rational r1(j, 1);
    for (int i = 0; i < n + 1; i++)
        lin[i] *= r1;
    return *this;
}

void LinExpr::print(ostream& os) const {
    //
    // print the contents into os
    //

    int j;
    bool sp = false;

    if (is_constant() && lin[n] == 0) {
        os << "0";
        return;
    }

    for (j = 0; j < n; ++j) {
        if (lin[j] == 0)
            continue;
        if (!sp) {
            sp = true;
            os << lin[j] << " * " << info->getName(j) << " ";
        } else {
            if (!(lin[j] < 0))
                os << " + ";

            os << lin[j] << " * " << info->getName(j) << " ";
        }
    }
    if (lin[n] == 0)
        return;

    if (!(lin[n] < 0))
        os << " + ";

    os << lin[n];

    return;
}

ostream& operator<<(ostream& os, LinExpr const& expr) {
    expr.print(os);
    return os;
}

int LinExpr::getDim() const {
    return n;
}
var_info* LinExpr::getInfo() const {
    return info;
}

int LinExpr::getDenLcm() const {
    int run = 1, j;
    for (int i = 0; i < n + 1; i++) {
        if ((j = lin[i].den()) != 0)  // Zero denominators are catastrophical..
            run = lcm(run, j);
    }
    return run;
}

int LinExpr::getNumGcd() const {
    bool first_number_seen = false;

    int run = 1, j;
    for (int i = 0; i < n + 1; i++) {
        if ((j = lin[i].num()) != 0) {
            if (first_number_seen)
                run = gcd(run, j);
            else {
                first_number_seen = true;
                run = j;
            }
        }
    }
    return run;
}

bool LinExpr::equiv(LinExpr const& tempExpr, Rational& factor) const {
    // Check if there is a multiplying factor such that  c * this =  l_2
    // Assert tempExpr!=0

    int i = 0;

    while (i < n + 1 && lin[i] == 0) {
        if (tempExpr(i) != 0)
            return false;
        i++;
    }

    factor = tempExpr(i) * lin[i].inverse();

    while (i < n + 1) {
        if (factor * lin[i] != tempExpr(i))
            return false;
        i++;
    }
    return true;
}

int LinExpr::resetCounter() {
    int t = count;
    count = 0;
    return t;
}

int LinExpr::count_up() {
    return count++;
}

int LinExpr::count_down() {
    return count--;
}

Linear_Expression LinExpr::toLinExpression() const {
    int j = getDenLcm();
    int num, den;
    num = lin[n].num();
    den = lin[n].den();
    Linear_Expression l(num * j / den);  // set the constant term
    for (int i = 0; i < n; i++) {
        num = lin[i].num();
        den = lin[i].den();
        l = l + (num * j / den) * Variable(i);
    }
    return l;
}

Constraint LinExpr::get_constraint(int ineqType) const {
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

// ***
// Old version, StInG compling under PPL 1.2 (05/11/2021),
// updates by Hongming Liu, in Shanghai Jiao Tong University.
// ***
/*
Rational LinExpr::evaluate(Generator const & g){
   Rational ret;// always initializes to 0
   Linear_Expression l1(g);
   int m;
   for(int i=0;i<n;i++){
      m=handleInt(l1.coefficient(Variable(i)));
      ret=ret+ m* lin[i];
   }
   ret=ret+lin[n];

   return ret;
}
*/

// ***
// New version, StInG compling under PPL 1.2 (05/11/2021),
// updates by Hongming Liu, in Shanghai Jiao Tong University.
// ***
Rational LinExpr::evaluate(Generator const& g) {
    Rational ret;  // always initializes to 0
    Linear_Expression l1;
    for (dimension_type i = g.space_dimension(); i-- > 0;) {
        l1 += g.coefficient(Variable(i)) * Variable(i);
    }

    int m;
    for (int i = 0; i < n; i++) {
        m = handleInt(l1.coefficient(Variable(i)));
        ret = ret + m * lin[i];
    }
    ret = ret + lin[n];

    return ret;
}
