
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

#include "ExpressionStore.h"

#include <iostream>
#include <vector>

#include "Expression.h"
#include "LinTransform.h"
#include "MatrixStore.h"
#include "Rational.h"
#include "SparseLinExpr.h"

void ExpressionStore::initialize(int vars_num, int lambda_num, var_info* dual_info, var_info* lambda_info) {
    this->vars_num = vars_num;
    this->lambda_num = lambda_num;
    this->dual_info = dual_info;
    this->lambda_info = lambda_info;

    le_list = new vector<SparseLinExpr>();
    lt_list = new vector<LinTransform>();
    /*
    m.init_set(vars_num,dual_info);
    split_seq=new vector<LinTransform>();
    vl = new vector<Expression>();
    */
}

ExpressionStore::ExpressionStore(int vars_num, int lambda_num, var_info* dual_info, var_info* lambda_info) {
    initialize(vars_num, lambda_num, dual_info, lambda_info);
}

bool ExpressionStore::add_expression(Expression& exp) {
    Expression* e = new Expression(exp);

    /* if (exp.is_pure_a()){
       add_linear_expression(e->convert_linear());
       return true;
       } */

    vl->push_back(*e);
    return false;
}

/*
void ExpressionStore::add_linear_expression(SparseLinExpr  exp){
   m.add_constraint(exp);

}
*/

void ExpressionStore::add_transform(LinTransform lt) {
    vector<Expression>::iterator vi;

    for (vi = vl->begin(); vi < vl->end(); vi++) {
        (*vi).transform(lt);
    }
}

void ExpressionStore::remove_trivial() {
    // look for zero expressions and remove them vector<Expression >::iterator
    // vi;
    vector<Expression>::iterator vi;
    vi = vl->begin();
    while (vi < vl->end() && (*vi).is_zero()) {
        vl->erase(vi);
        vi = vl->begin();
    }

    for (; vi < vl->end(); vi++) {
        if ((*vi).is_zero()) {
            vl->erase(vi);
            vi--;
        }
    }

    return;
}

/*
bool ExpressionStore::is_consistent(){

   if (!m.is_consistent()){
      return false;
   }

   vector<Expression >::iterator vi;

   for (vi=vl->begin();vi < vl->end();vi ++){
      if ((*vi).is_inconsistent()) {
         return false;
      }
   }

   return true;


}

*/

void ExpressionStore::simplify(MatrixStore const& m) {
    //   bool info=true;
    vector<Expression>::iterator vi;
    SparseLinExpr ll;
    LinTransform lt(vars_num, dual_info);

    //   while (info){

    remove_trivial();

    // Now take each expression and simplify it

    for (vi = vl->begin(); vi < vl->end(); vi++)
        (*vi).simplify(m);

    /* This can only be done for equality stores
       for (vi=vl->begin();vi <vl->end();vi++){
       if ((*vi).is_pure_a()){
       info=true;

       ll=(*vi).convert_linear();
       cout<<"Adding Lin Exp"<< ll<<endl;
       add_linear_expression(ll);
       } else if ((*vi).is_pure_b()){
       info=true;
       lt=(*vi).convert_transform();
       add_transform(lt);
       cout<<"Adding Linear Transform "<<lt<<endl;
       }

    }

    */
    remove_trivial();

    //}

    return;
}

/*
MatrixStore & ExpressionStore::get_m(){
   return m;
}

*/
vector<Expression>* ExpressionStore::get_vl() {
    return vl;
}

ostream& operator<<(ostream& os, ExpressionStore& es) {
    vector<Expression>::iterator vi;
    vector<Expression>* vl = es.get_vl();
    os << "The Expressions are:" << endl;
    for (vi = vl->begin(); vi < vl->end(); vi++) {
        os << (*vi) << endl;
    }

    return os;
}

vector<SparseLinExpr>::iterator ExpressionStore::lin_expr_collected(
    SparseLinExpr const& l) const {
    vector<SparseLinExpr>::iterator vi;
    for (vi = le_list->begin(); vi < le_list->end(); vi++) {
        if ((*vi) == l)
            return vi;
    }

    return vi;
}

vector<LinTransform>::iterator ExpressionStore::lin_transform_collected(
    LinTransform const& l) const {
    vector<LinTransform>::iterator vi;
    for (vi = lt_list->begin(); vi < lt_list->end(); vi++) {
        if ((*vi) == l)
            return vi;
    }

    return vi;
}

bool ExpressionStore::collect_factors() {
    vector<Expression>::iterator vi;
    vector<SparseLinExpr>::iterator vj;
    vector<LinTransform>::iterator vk;
    bool some = false;
    for (vi = vl->begin(); vi < vl->end(); vi++) {
        if ((*vi).factorize()) {
            some = true;
            vj = lin_expr_collected((*vi).get_linear_factor());
            if (vj < le_list->end())
                (*vj).count_up();
            else
                le_list->push_back((*vi).get_linear_factor());

            vk = lin_transform_collected((*vi).get_transform_factor());

            if (vk < lt_list->end())
                (*vk).count_up();
            else
                lt_list->push_back((*vi).get_transform_factor());
        }
    }

    cout << "Collecting Factors:" << endl;

    for (vj = le_list->begin(); vj < le_list->end(); vj++)
        cout << (*vj) << "  Occurs " << (*vj).get_count() << endl;

    for (vk = lt_list->begin(); vk < lt_list->end(); vk++)
        cout << (*vk) << "  Occurs  " << (*vk).get_count() << endl;

    return some;
}