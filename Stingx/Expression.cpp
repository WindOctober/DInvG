
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

#include "Expression.h"

#include "LinTransform.h"
#include "MatrixStore.h"
#include "Rational.h"
#include "SparseLinExpr.h"
#include "funcs.h"
#include "myassertions.h"
#include "var-info.h"

void Expression::initialize(int coefNum,
                            int lambdaNum,
                            var_info* coefInfo,
                            var_info* lambdaInfo) {
    // Initialize the parameters of the class
    this->coefNum = coefNum;
    this->lambdaNum = lambdaNum;
    this->coefInfo = coefInfo;
    this->lambdaInfo = lambdaInfo;
    factored = false;
    linExpr.resize(lambdaNum + 1, SparseLinExpr(coefNum, coefInfo));
    count = 0;
}

void Expression::zero_out() {
    // set the whole expression to zero
    // Post-comment== Is this being called from somewhere?
    for (int i = 0; i < lambdaNum + 1; i++)
        linExpr[i].init_set(coefNum, coefInfo);
}

Expression::Expression(int coefNum,
                       int lambdaNum,
                       var_info* coefInfo,
                       var_info* lambdaInfo) {
    initialize(coefNum, lambdaNum, coefInfo, lambdaInfo);
}

Expression::~Expression() {
    // delete[] l;
}

Expression::Expression(Expression* e1, Expression* e2) {
    initialize(e1->get_n(), e1->get_r(), e1->get_fn(), e1->get_fr());
    int i;
    for (i = 0; i < lambdaNum + 1; i++)
        linExpr[i] = (*e1)[i] - (*e2)[i];
}

Expression::Expression(Expression const& e) {
    initialize(e.get_n(), e.get_r(), e.get_fn(), e.get_fr());
    int i;
    for (i = 0; i < lambdaNum + 1; i++)
        linExpr[i] = e(i);
    if (e.is_factored())
        factorize();
}

Expression& Expression::operator=(Expression const& p1) {
    // initialize(p1.get_n(),p1.get_r(),p1.get_fn(),p1.get_fr());
    for (int i = 0; i < lambdaNum + 1; i++)
        linExpr[i] = p1(i);

    return (*this);
}

SparseLinExpr& Expression::operator[](int i) {
    return linExpr[i];
}

SparseLinExpr Expression::operator()(int i) const {
    return linExpr[i];
}

int Expression::get_n() const {
    return coefNum;
}
int Expression::get_r() const {
    return lambdaNum;
}
var_info* Expression::get_fr() const {
    return lambdaInfo;
}
var_info* Expression::get_fn() const {
    return coefInfo;
}

bool Expression::is_pure_a() const {
    // check if for each of the expression l[0].. l[lambdaNum-1]
    // is zero

    for (int i = 0; i < lambdaNum; i++)
        if (!linExpr[i].isZero())
            return false;

    return true;
}

bool Expression::is_pure_b() const {
    // check if each l[0]... l[lambdaNum] is a constant

    for (int i = 0; i < lambdaNum + 1; i++)
        if (!linExpr[i].is_constant())
            return false;

    return true;
}

SparseLinExpr& Expression::convert_linear() {
    // Call if only the expression is pure a
    if (!is_pure_a()) {
        cerr << "Expression::convert_linear-- Asked to convert an expression "
                "that "
                "fails Expression::is_pure_a()"
             << endl
             << "Exiting in Panic.... " << endl;
        exit(1);
    }

    return linExpr[lambdaNum];  // That does it
}

LinTransform Expression::convert_transform() const {
    //
    // precondition: This is actually a transform
    // assuming this blindly convert.
    //

    LinTransform tmp(lambdaNum, lambdaInfo);
    SparseLinExpr temp;

    for (int i = 0; i < lambdaNum + 1; i++) {
        tmp[i] = (linExpr[i])(coefNum);  // set it to a constant
    }
    return tmp;
}

void Expression::transform(LinTransform& lin) {
    if (lin.is_trivial() || lin.is_inconsistent())
        return;  // Nothing to be done here

    int base = lin.getBase();
    assert(lin(base)==1);
    for (int i = base + 1; i < lambdaNum + 1; i++)
        linExpr[i] = linExpr[i] - lin(i) * linExpr[base];

    linExpr[base] *= 0;  // kill the base
                          // That completes the transformation
}

void Expression::simplify(MatrixStore const& c) {
    for (int i = 0; i < lambdaNum + 1; i++)
        c.simplify(linExpr[i]);
    return;
}

bool Expression::is_constant() const {
    // Check if each of the lambdaNum non-linear terms are zero and the last one
    // is a constant

    int i;

    for (i = 0; i < lambdaNum; i++)
        if (!linExpr[i].isZero())
            return false;

    if (linExpr[lambdaNum].is_constant())
        return true;

    return false;
}

bool Expression::isZero() const {
    int i;

    for (i = 0; i < lambdaNum + 1; i++)
        if (!linExpr[i].isZero())
            return false;

    return true;
}

bool Expression::is_inconsistent() const {
    int i;

    for (i = 0; i < lambdaNum; i++)
        if (!linExpr[i].isZero())
            return false;

    if (linExpr[lambdaNum].is_constant() && !linExpr[lambdaNum].isZero())
        return true;

    return false;
}

int Expression::get_denominator_lcm() const {
    int run = 1, j;
    for (int i = 0; i < lambdaNum + 1; i++) {
        if ((j = linExpr[i].get_denominator_lcm()) != 0)
            run = lcm(run, j);
    }
    return run;
}

int Expression::get_numerator_gcd() const {
    bool first_number_seen = false;

    int run = 1, j;
    for (int i = 0; i < lambdaNum + 1; i++) {
        if ((j = linExpr[i].get_numerator_gcd()) != 0) {
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

void Expression::adjust() {
    int i = get_denominator_lcm(), j = get_numerator_gcd();
    if (j == 0)
        return;  // Nothing much to be done here.. constraint should not have
                 // been there.

    Rational r1(i, j);

    for (i = 0; i < lambdaNum + 1; i++)
        linExpr[i] *= r1;

    return;
}

bool Expression::is_factored() const {
    return factored;
}

void Expression::print_factors(ostream& os) const {
    os << " ( " << transFact << " ) * ( " << linFact << " ) ";
}
ostream& operator<<(ostream& os, Expression const& expr) {
    os << "├ ";
    if (expr.is_factored()) {
        expr.print_factors(os);
    } else {
        int lambdaNum = expr.get_r();
        var_info* lambdaInfo = expr.get_fr();

        os << lambdaInfo->get_name(0) << " * (" << expr(0) << " ) ";
        for (int i = 1; i < lambdaNum; i++) {
            os << " + " << lambdaInfo->get_name(i) << " * ( " << expr(i)
               << " ) ";
        }

        os << " + " << expr(lambdaNum) << "  ";
    }
    return os;
}

bool Expression::factorize() {
    int i = 0, j;
    Rational factor;
    while (i < lambdaNum + 1 && linExpr[i].isZero()) {
        i++;
    }

    if (i >= lambdaNum + 1)
        return false;
    // DETECT trivial terms and take them out
    j = i;
    LinTransform t(lambdaNum, lambdaInfo);

    t[j] = 1;
    for (i = j + 1; i < lambdaNum + 1; i++) {
        if (!linExpr[j].equiv(linExpr[i], factor))
            return false;
        t[i] = factor;
    }

    transFact = t; // NOTE: j 所在的位置就是 \mu所在的位置，所以这里的系数是1，t记录的就是(\mu - a) \alpha中的 \mu和a前面的系数
    linFact = linExpr[j]; //NOTE : 记录的是\alpha，也就是后面的对应系数的表达式。

    factored = true;
    return true;
}

SparseLinExpr& Expression::getLinFactor() {
    return linFact;
}

LinTransform& Expression::getTransformFactor() {
    return transFact;
}

Expression* Expression::clone() const {
    // create a new expression
    Expression* ret = new Expression(coefNum, lambdaNum, coefInfo, lambdaInfo);
    for (int i = 0; i < lambdaNum + 1; i++) {
        (*ret)[i] = linExpr[i];  // Assign the appropriate linear expressions
    }
    ret->factorize();  // so that the factored representation may be filled in

    return ret;
}

void Expression::resetCounter() {
    count = 0;
}

void Expression::add_count(int i) {
    count += i;
}

int Expression::getCount() {
    return count;
}

bool Expression::transform_matches(LinTransform& lt) {
    if (!factorize())
        return false;
    return (lt == transFact);
}

void Expression::drop_transform(LinTransform& lt) {
    if (transform_matches(lt)) {
        int i;
        for (i = 0; i < lambdaNum; i++)
            linExpr[i] *= 0;

        linExpr[lambdaNum] = linFact;
        factored = false;
    }
    return;
}

SparseLinExpr Expression::to_transform(Generator const& g) {
    SparseLinExpr ret(lambdaNum, lambdaInfo);
    for (int i = 0; i < lambdaNum + 1; i++) {
        ret.set_coefficient(
            i,
            linExpr[i].evaluate(
                g));  // Evaluate the value of l[i] under the generator g
    }

    return ret;
}

void Expression::count_multipliers(int* t) {
    // assume t[0..lambdaNum-1] is an allocated array or suffer the core dump!
    for (int i = 0; i < lambdaNum; i++)
        if (!(*this)(i).isZero()) {
            t[i]++;
        }
    return;
}

bool Expression::is_multiplier_present(int index) {
    PRECONDITION((index >= 0 && index < lambdaNum),
                 " expression::is_multiplier_present() -- illegal index");

    return !(linExpr[index].isZero());
}
