
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

void Expression::initialize(int n, int r, var_info* fn, var_info* fr) {
    // Initialize the parameters of the class
    this->n = n;
    this->r = r;
    this->fn = fn;
    this->fr = fr;
    factored = false;
    l.resize(r + 1, SparseLinExpr(n, fn));
    count = 0;
}

void Expression::zero_out() {
    // set the whole expression to zero
    // Post-comment== Is this being called from somewhere?

    int i;
    for (i = 0; i < r + 1; i++)
        l[i].init_set(n, fn);
}

Expression::Expression(int n, int r, var_info* fn, var_info* fr) {
    initialize(n, r, fn, fr);
}

Expression::~Expression() {
    // delete[] l;
}

Expression::Expression(Expression* e1, Expression* e2) {
    initialize(e1->get_n(), e1->get_r(), e1->get_fn(), e1->get_fr());
    int i;
    for (i = 0; i < r + 1; i++)
        l[i] = (*e1)[i] - (*e2)[i];
}

Expression::Expression(Expression const& e) {
    initialize(e.get_n(), e.get_r(), e.get_fn(), e.get_fr());
    int i;
    for (i = 0; i < r + 1; i++)
        l[i] = e(i);
    if (e.is_factored())
        factorize();
}

Expression Expression::operator+(Expression const& p1) const {
    Expression temp(n, r, fn, fr);
    int i;
    for (i = 0; i < r + 1; i++)
        temp[r] = l[r] + p1(r);

    return temp;
}

Expression& Expression::operator+=(Expression const& p1) {
    int i;

    for (i = 0; i < r + 1; i++)
        l[r] += p1(r);

    return *this;
}

Expression Expression::operator-(Expression const& p1) const {
    Expression temp(n, r, fn, fr);
    int i;
    for (i = 0; i < r + 1; i++)
        temp[r] = l[r] - p1(r);

    return temp;
}

Expression& Expression::operator-=(Expression const& p1) {
    int i;
    for (i = 0; i < r + 1; i++)
        l[r] -= p1(r);

    return *this;
}

Expression& Expression::operator=(Expression const& p1) {
    // initialize(p1.get_n(),p1.get_r(),p1.get_fn(),p1.get_fr());
    for (int i = 0; i < r + 1; i++)
        l[i] = p1(i);

    return (*this);
}

SparseLinExpr& Expression::operator[](int i) {
    return l[i];
}

SparseLinExpr Expression::operator()(int i) const {
    return l[i];
}

int Expression::get_n() const {
    return n;
}
int Expression::get_r() const {
    return r;
}
var_info* Expression::get_fr() const {
    return fr;
}
var_info* Expression::get_fn() const {
    return fn;
}

bool Expression::is_pure_a() const {
    // check if for each of the expression l[0].. l[r-1]
    // is zero

    for (int i = 0; i < r; i++)
        if (!l[i].is_zero())
            return false;

    return true;
}

bool Expression::is_pure_b() const {
    // check if each l[0]... l[r] is a constant

    for (int i = 0; i < r + 1; i++)
        if (!l[i].is_constant())
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

    return l[r];  // That does it
}

LinTransform Expression::convert_transform() const {
    //
    // precondition: This is actually a transform
    // assuming this blindly convert.
    //

    LinTransform tmp(r, fr);
    SparseLinExpr temp;

    for (int i = 0; i < r + 1; i++) {
        tmp[i] = (l[i])(n);  // set it to a constant
    }
    return tmp;
}

void Expression::transform(LinTransform& lin) {
    if (lin.is_trivial() || lin.is_inconsistent())
        return;  // Nothing to be done here

    int base = lin.get_base();

    for (int i = base + 1; i < r + 1; i++)
        l[i] = lin(base) * l[i] - lin(i) * l[base];

    l[base] *= 0;  // kill the base
                   // That completes the transformation
}

void Expression::simplify(MatrixStore const& c) {
    for (int i = 0; i < r + 1; i++)
        c.simplify(l[i]);
    return;
}

bool Expression::is_constant() const {
    // Check if each of the r non-linear terms are zero and the last one is a
    // constant

    int i;

    for (i = 0; i < r; i++)
        if (!l[i].is_zero())
            return false;

    if (l[r].is_constant())
        return true;

    return false;
}

bool Expression::is_zero() const {
    int i;

    for (i = 0; i < r + 1; i++)
        if (!l[i].is_zero())
            return false;

    return true;
}

bool Expression::is_inconsistent() const {
    int i;

    for (i = 0; i < r; i++)
        if (!l[i].is_zero())
            return false;

    if (l[r].is_constant() && !l[r].is_zero())
        return true;

    return false;
}

int Expression::get_denominator_lcm() const {
    int run = 1, j;
    for (int i = 0; i < r + 1; i++) {
        if ((j = l[i].get_denominator_lcm()) != 0)
            run = lcm(run, j);
    }
    return run;
}

int Expression::get_numerator_gcd() const {
    bool first_number_seen = false;

    int run = 1, j;
    for (int i = 0; i < r + 1; i++) {
        if ((j = l[i].get_numerator_gcd()) != 0) {
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

    for (i = 0; i < r + 1; i++)
        l[i] *= r1;

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
        int r = expr.get_r();
        var_info* fr = expr.get_fr();

        os << fr->get_name(0) << " * (" << expr(0) << " ) ";
        for (int i = 1; i < r; i++) {
            os << " + " << fr->get_name(i) << " * ( " << expr(i) << " ) ";
        }

        os << " + " << expr(r) << "  ";
    }
    return os;
}

/*
void Expression::compute_dpl_form(){
   // compute the internal saclib representation
   //by convention, <non-linear-variables> 0... r-1  > linears 1... n-1
   // first compute the dpl representation and then the rec representation

   Word pl1,term=NIL;
   int i,j;
   int dummy;
   int * t= new int[n+r];
   int coeff;
   adjust();
   for(i=0;i<n+r;i++)
      t[i]=0;

   for(i=0;i<r;i++){
      t[i]=1;
      for(j=0;j<n;j++){
         t[r+j]=1;
         coeff=l[i][j].num();
         term=listify(t,n+r);
         t[r+j]=0;
         DIPINS(coeff,term,pl,&dummy,&pl1);
         pl=pl1;
      }
      coeff=l[i][n].num();
      term=listify(t,n+r);
       DIPINS(coeff,term,pl,&dummy,&pl1);
       pl=pl1;
       t[i]=0;
   }
   for(j=0;j<n;j++){
         t[r+j]=1;
         coeff=l[r][j].num();
         term=listify(t,n+r);
         t[r+j]=0;
         DIPINS(coeff,term,pl,&dummy,&pl1);
         pl=pl1;
      }


    coeff=l[r][n].num();
    term=listify(t,n+r);
    DIPINS(coeff,term,pl,&dummy,&pl1);
    pl=PFDIP(r+n,pl1);


}

*/
bool Expression::factorize() {
    /*
    compute_dpl_form(); // compute the polynomial
    int s,c,i,j,k;
    Word L0,L,L1,L2;
    Word term;
    IPFAC(n+r,pl,&s,&c,&L);
    // Now interpret the result in L in terms of the factors.

    AWRITE(L);
    parse_factored(L);
    return true;
    */

    // For the time being I shall just factor this by myself instead of
    // compiling in/out of the SACLIB representation

    // Detect the first non-zero linear expression

    int i;
    int i0;
    i = 0;
    Rational factor;
    while (i < r + 1 && l[i].is_zero())
        i++;

    // l[i]!=0
    if (i >= r + 1)
        return false;  // DO NOT ALLOW THIS TO HAPPEN
    // DETECT trivial terms and take them out

    i0 = i;
    LinTransform t(r, fr);

    t[i0] = 1;
    for (i = i0 + 1; i < r + 1; i++) {
        if (!l[i0].equiv(l[i], factor))
            return false;
        t[i] = factor;
    }

    // For the time being just write down the factors
    tr_fact = t;
    lin_fact = l[i0];

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
    Expression* ret = new Expression(n, r, fn, fr);
    for (int i = 0; i < r + 1; i++) {
        (*ret)[i] = l[i];  // Assign the appropriate linear expressions
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
        for (i = 0; i < r; i++)
            l[i] *= 0;

        l[r] = lin_fact;
        factored = false;
    }
    return;
}

SparseLinExpr Expression::to_transform(Generator const& g) {
    SparseLinExpr ret(r, fr);
    for (int i = 0; i < r + 1; i++) {
        ret.set_coefficient(
            i,
            l[i].evaluate(
                g));  // Evaluate the value of l[i] under the generator g
    }

    return ret;
}

void Expression::count_multipliers(int* t) {
    // assume t[0..r-1] is an allocated array or suffer the core dump!
    for (int i = 0; i < r; i++)
        if (!(*this)(i).is_zero()) {
            t[i]++;
        }
    return;
}

bool Expression::is_multiplier_present(int index) {
    PRECONDITION((index >= 0 && index < r),
                 " expression::is_multiplier_present() -- illegal index");

    return !(l[index].is_zero());
}
