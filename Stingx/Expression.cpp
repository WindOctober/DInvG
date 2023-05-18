
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

void Expression::initialize(int dual_num, int lambda_num, var_info* dual_info, var_info* lambda_info) {
    // Initialize the parameters of the class
    this->dual_num = dual_num;
    this->lambda_num = lambda_num;
    this->dual_info = dual_info;
    this->lambda_info = lambda_info;
    factored = false;
    lin_expr.resize(lambda_num + 1, SparseLinExpr(dual_num, dual_info));
    count = 0;
}

void Expression::zero_out() {
    // set the whole expression to zero
    // Post-comment== Is this being called from somewhere?
    for (int i = 0; i < lambda_num + 1; i++)
        lin_expr[i].init_set(dual_num, dual_info);
}

Expression::Expression(int dual_num, int lambda_num, var_info* dual_info, var_info* lambda_info) {
    initialize(dual_num, lambda_num, dual_info, lambda_info);
}

Expression::~Expression() {
    // delete[] l;
}

Expression::Expression(Expression* e1, Expression* e2) {
    initialize(e1->get_n(), e1->get_r(), e1->get_fn(), e1->get_fr());
    int i;
    for (i = 0; i < lambda_num + 1; i++)
        lin_expr[i] = (*e1)[i] - (*e2)[i];
}

Expression::Expression(Expression const& e) {
    initialize(e.get_n(), e.get_r(), e.get_fn(), e.get_fr());
    int i;
    for (i = 0; i < lambda_num + 1; i++)
        lin_expr[i] = e(i);
    if (e.is_factored())
        factorize();
}

Expression Expression::operator+(Expression const& p1) const {
    Expression temp(dual_num, lambda_num, dual_info, lambda_info);
    int i;
    for (i = 0; i < lambda_num + 1; i++)
        temp[lambda_num] = lin_expr[lambda_num] + p1(lambda_num);

    return temp;
}

Expression& Expression::operator+=(Expression const& p1) {
    int i;

    for (i = 0; i < lambda_num + 1; i++)
        lin_expr[lambda_num] += p1(lambda_num);

    return *this;
}

Expression Expression::operator-(Expression const& p1) const {
    Expression temp(dual_num, lambda_num, dual_info, lambda_info);
    int i;
    for (i = 0; i < lambda_num + 1; i++)
        temp[lambda_num] = lin_expr[lambda_num] - p1(lambda_num);

    return temp;
}

Expression& Expression::operator-=(Expression const& p1) {
    int i;
    for (i = 0; i < lambda_num + 1; i++)
        lin_expr[lambda_num] -= p1(lambda_num);

    return *this;
}

Expression& Expression::operator=(Expression const& p1) {
    // initialize(p1.get_n(),p1.get_r(),p1.get_fn(),p1.get_fr());
    for (int i = 0; i < lambda_num + 1; i++)
        lin_expr[i] = p1(i);

    return (*this);
}

SparseLinExpr& Expression::operator[](int i) {
    return lin_expr[i];
}

SparseLinExpr Expression::operator()(int i) const {
    return lin_expr[i];
}

int Expression::get_n() const {
    return dual_num;
}
int Expression::get_r() const {
    return lambda_num;
}
var_info* Expression::get_fr() const {
    return lambda_info;
}
var_info* Expression::get_fn() const {
    return dual_info;
}

bool Expression::is_pure_a() const {
    // check if for each of the expression l[0].. l[lambda_num-1]
    // is zero

    for (int i = 0; i < lambda_num; i++)
        if (!lin_expr[i].is_zero())
            return false;

    return true;
}

bool Expression::is_pure_b() const {
    // check if each l[0]... l[lambda_num] is a constant

    for (int i = 0; i < lambda_num + 1; i++)
        if (!lin_expr[i].is_constant())
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

    return lin_expr[lambda_num];  // That does it
}

LinTransform Expression::convert_transform() const {
    //
    // precondition: This is actually a transform
    // assuming this blindly convert.
    //

    LinTransform tmp(lambda_num, lambda_info);
    SparseLinExpr temp;

    for (int i = 0; i < lambda_num + 1; i++) {
        tmp[i] = (lin_expr[i])(dual_num);  // set it to a constant
    }
    return tmp;
}

void Expression::transform(LinTransform& lin) {
    if (lin.is_trivial() || lin.is_inconsistent())
        return;  // Nothing to be done here

    int base = lin.get_base();

    for (int i = base + 1; i < lambda_num + 1; i++)
        lin_expr[i] = lin(base) * lin_expr[i] - lin(i) * lin_expr[base];

    lin_expr[base] *= 0;  // kill the base
                   // That completes the transformation
}

void Expression::simplify(MatrixStore const& c) {
    for (int i = 0; i < lambda_num + 1; i++)
        c.simplify(lin_expr[i]);
    return;
}

bool Expression::is_constant() const {
    // Check if each of the lambda_num non-linear terms are zero and the last one is a
    // constant

    int i;

    for (i = 0; i < lambda_num; i++)
        if (!lin_expr[i].is_zero())
            return false;

    if (lin_expr[lambda_num].is_constant())
        return true;

    return false;
}

bool Expression::is_zero() const {
    int i;

    for (i = 0; i < lambda_num + 1; i++)
        if (!lin_expr[i].is_zero())
            return false;

    return true;
}

bool Expression::is_inconsistent() const {
    int i;

    for (i = 0; i < lambda_num; i++)
        if (!lin_expr[i].is_zero())
            return false;

    if (lin_expr[lambda_num].is_constant() && !lin_expr[lambda_num].is_zero())
        return true;

    return false;
}

int Expression::get_denominator_lcm() const {
    int run = 1, j;
    for (int i = 0; i < lambda_num + 1; i++) {
        if ((j = lin_expr[i].get_denominator_lcm()) != 0)
            run = lcm(run, j);
    }
    return run;
}

int Expression::get_numerator_gcd() const {
    bool first_number_seen = false;

    int run = 1, j;
    for (int i = 0; i < lambda_num + 1; i++) {
        if ((j = lin_expr[i].get_numerator_gcd()) != 0) {
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

    for (i = 0; i < lambda_num + 1; i++)
        lin_expr[i] *= r1;

    return;
}

bool Expression::is_factored() const {
    return factored;
}

void Expression::print_factors(ostream& os) const {
    os << " ( " << tr_fact << " ) * ( " << lin_fact << " ) ";
}
ostream& operator<<(ostream& os, Expression const& expr) {
    os << "├ ";
    if (expr.is_factored()) {
        expr.print_factors(os);
    } else {
        int lambda_num = expr.get_r();
        var_info* lambda_info = expr.get_fr();

        os << lambda_info->get_name(0) << " * (" << expr(0) << " ) ";
        for (int i = 1; i < lambda_num; i++) {
            os << " + " << lambda_info->get_name(i) << " * ( " << expr(i) << " ) ";
        }

        os << " + " << expr(lambda_num) << "  ";
    }
    return os;
}

/*
void Expression::compute_dpl_form(){
   // compute the internal saclib representation
   //by convention, <non-linear-variables> 0... lambda_num-1  > linears 1... dual_num-1
   // first compute the dpl representation and then the rec representation

   Word pl1,term=NIL;
   int i,j;
   int dummy;
   int * t= new int[dual_num+lambda_num];
   int coeff;
   adjust();
   for(i=0;i<dual_num+lambda_num;i++)
      t[i]=0;

   for(i=0;i<lambda_num;i++){
      t[i]=1;
      for(j=0;j<dual_num;j++){
         t[lambda_num+j]=1;
         coeff=l[i][j].num();
         term=listify(t,dual_num+lambda_num);
         t[lambda_num+j]=0;
         DIPINS(coeff,term,pl,&dummy,&pl1);
         pl=pl1;
      }
      coeff=l[i][dual_num].num();
      term=listify(t,dual_num+lambda_num);
       DIPINS(coeff,term,pl,&dummy,&pl1);
       pl=pl1;
       t[i]=0;
   }
   for(j=0;j<dual_num;j++){
         t[lambda_num+j]=1;
         coeff=l[lambda_num][j].num();
         term=listify(t,dual_num+lambda_num);
         t[lambda_num+j]=0;
         DIPINS(coeff,term,pl,&dummy,&pl1);
         pl=pl1;
      }


    coeff=l[lambda_num][dual_num].num();
    term=listify(t,dual_num+lambda_num);
    DIPINS(coeff,term,pl,&dummy,&pl1);
    pl=PFDIP(lambda_num+dual_num,pl1);


}

*/
bool Expression::factorize() {
    int i;
    int i0;
    i = 0;
    Rational factor;
    while (i < lambda_num + 1 && lin_expr[i].is_zero()){
        i++;
        cout<<i<<endl;
    }

    if (i >= lambda_num + 1)
        return false;  // DO NOT ALLOW THIS TO HAPPEN
    // DETECT trivial terms and take them out
    i0 = i;
    LinTransform t(lambda_num, lambda_info);

    t[i0] = 1;
    for (i = i0 + 1; i < lambda_num + 1; i++) {
        if (!lin_expr[i0].equiv(lin_expr[i], factor))
            return false;
        t[i] = factor;
    }

    // For the time being just write down the factors
    tr_fact = t;
    lin_fact = lin_expr[i0];

    factored = true;
    return true;
}

SparseLinExpr& Expression::get_linear_factor() {
    return lin_fact;
}

LinTransform& Expression::get_transform_factor() {
    return tr_fact;
}

Expression* Expression::clone() const {
    // create a new expression
    Expression* ret = new Expression(dual_num, lambda_num, dual_info, lambda_info);
    for (int i = 0; i < lambda_num + 1; i++) {
        (*ret)[i] = lin_expr[i];  // Assign the appropriate linear expressions
    }
    ret->factorize();  // so that the factored representation may be filled in

    return ret;
}

void Expression::reset_count() {
    count = 0;
}

void Expression::add_count(int i) {
    count += i;
}

int Expression::get_count() {
    return count;
}

bool Expression::transform_matches(LinTransform& lt) {
    if (!factorize())
        return false;

    return (lt == tr_fact);
}

void Expression::drop_transform(LinTransform& lt) {
    if (transform_matches(lt)) {
        int i;
        for (i = 0; i < lambda_num; i++)
            lin_expr[i] *= 0;

        lin_expr[lambda_num] = lin_fact;
        factored = false;
    }
    return;
}

SparseLinExpr Expression::to_transform(Generator const& g) {
    SparseLinExpr ret(lambda_num, lambda_info);
    for (int i = 0; i < lambda_num + 1; i++) {
        ret.set_coefficient(
            i,
            lin_expr[i].evaluate(
                g));  // Evaluate the value of l[i] under the generator g
    }

    return ret;
}

void Expression::count_multipliers(int* t) {
    // assume t[0..lambda_num-1] is an allocated array or suffer the core dump!
    for (int i = 0; i < lambda_num; i++)
        if (!(*this)(i).is_zero()) {
            t[i]++;
        }
    return;
}

bool Expression::is_multiplier_present(int index) {
    PRECONDITION((index >= 0 && index < lambda_num),
                 " expression::is_multiplier_present() -- illegal index");

    return !(lin_expr[index].is_zero());
}
