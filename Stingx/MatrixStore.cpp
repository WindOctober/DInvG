
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

#include <iostream>
// #include <saclib.h>
#include "MatrixStore.h"
#include "SparseLinExpr.h"
#include "var-info.h"

MatrixStore::MatrixStore() {
    vars_num = 0;
    return;
}
void MatrixStore::initialize(int vars_num, var_info* info) {
    this->vars_num = vars_num;
    mat = new Rational*[vars_num];  // the last column is the $b$ augment
    for (int i = 0; i < vars_num; i++)
        mat[i] = new Rational[vars_num + 1];

    zero_out();  // wipe the matrices clear!
    this->info = info;
    consistent = true;
}

MatrixStore::MatrixStore(int vars_num, var_info* info) {
    initialize(vars_num, info);
}

void MatrixStore::zero_out() {
    for (int i = 0; i < vars_num; i++)
        for (int j = 0; j < vars_num + 1; j++)
            mat[i][j] = 0;
    consistent = true;
}

void MatrixStore::init_set(int vars_num, var_info* linear_var_info) {
    initialize(vars_num, linear_var_info);
}

int MatrixStore::simplify(SparseLinExpr& expression) const {
    // Use the guassian elimination type technique
    int i, j;
    int lead = vars_num + 1;
    Rational temp1, temp2;
    for (i = 0; i < vars_num; i++) {
        if (!(mat[i][i] == 0)) {
            if (expression(i) != 0) {
                // Perform a reduction of the expression
                for (j = 0; j < i; j++) {
                    temp2 = (expression(i) * mat[i][j]) * mat[i][i].inv();
                    expression.subtract_coefficient(j, temp2);
                }
                for (j = i + 1; j < vars_num + 1; j++) {
                    temp2 = (expression(i) * mat[i][j]) * mat[i][i].inv();
                    expression.subtract_coefficient(j, temp2);
                }
                expression.set_coefficient(i, 0);  // reset expression[i]
            }
        }
    }

    for (i = 0; i < vars_num + 1; i++) {
        if (expression(i) != 0) {
            lead = i;
            break;
        }
    }

    return lead;
}

void MatrixStore::back_substitute(int lead) {
    if (lead >= vars_num || mat[lead][lead] == 0)
        return;
    Rational temp1, temp2;
    int i, j;
    for (i = lead - 1; i >= 0; i--) {
        if (mat[i][lead] != 0) {
            for (j = lead + 1; j < vars_num + 1; j++) {
                temp1 = mat[i][j];
                temp2 = mat[lead][j] * mat[i][lead] * (mat[lead][lead].inv());
                mat[i][j] -= temp2;
            }
            mat[i][lead] = 0;
        }
    }
    return;
}

bool MatrixStore::add_constraint(SparseLinExpr& expression) {
    // First do the elimination from each row on expression
    int i;
    int lead =
        simplify(expression);  // Identify what the expression simplifies to

    if (lead >= vars_num) {
        if (expression(vars_num) != 0) {
            consistent = false;
            return false;
        } else
            return true;  // Nothing to be done for the constraint
    }

    // else copy the constraint to the lead row

    for (i = lead; i < vars_num + 1; i++)
        mat[lead][i] = expression(i);
    back_substitute(lead);
    return true;
}

bool MatrixStore::is_consistent() const {
    return consistent;
}

void MatrixStore::set_consistent(bool c) {
    consistent = c;
    return;
}
void MatrixStore::print() const {
    // print the constraints stored
    int i, j;
    bool some = false;
    cout << "├ ";
    for (i = 0; i < vars_num; i++) {
        if (mat[i][i] == 0)
            continue;
        some = true;
        cout << mat[i][i] << " * " << info->get_name(i);
        for (j = i + 1; j < vars_num; j++) {
            if (mat[i][j] == 0)
                continue;
            cout << "+" << mat[i][j] << " * " << info->get_name(j);
        }

        if (mat[i][vars_num] != 0) {
            cout << " + " << mat[i][vars_num];
        }
        cout << " = 0" << endl;
    }

    if (!some)
        cout << "Empty Store";
    cout << endl;
}

Rational& MatrixStore::operator()(int i, int j) {
    return mat[i][j];
}

ostream& operator<<(ostream& os, MatrixStore const& p) {
    // print the constraints stored
    int i, j;
    bool some = false;
    int vars_num = p.get_dim();

    var_info* info = p.get_info();
    Rational** mat = p.get_matrix();

    if (!p.is_consistent())
        cout << "Inconsistent" << endl;

    for (i = 0; i < vars_num; i++) {
        if (mat[i][i] == 0)
            continue;
        some = true;
        os << "├ ";
        os << mat[i][i] << " * " << info->get_name(i);
        for (j = i + 1; j < vars_num; j++) {
            if (mat[i][j] == 0)
                continue;
            os << "+" << mat[i][j] << " * " << info->get_name(j);
        }
        if (mat[i][vars_num] != 0) {
            os << " + " << mat[i][vars_num];
        }
        os << " = 0" << endl;
    }
    if (!some) {
        os << "├ ";
        os << "Empty Store" << endl;
    }

    return os;
}

int MatrixStore::get_dim() const {
    return vars_num;
}
var_info* MatrixStore::get_info() const {
    return info;
}

Rational** MatrixStore::get_matrix() const {
    return mat;
}

Constraint_System MatrixStore::to_constraint_system() const {
    SparseLinExpr l(vars_num, info);
    int i, j;
    Constraint_System ret;
    for (i = 0; i < vars_num; i++) {
        l.set_coefficient(vars_num, mat[i][vars_num]);
        for (j = 0; j < vars_num; j++) {
            l.set_coefficient(j, mat[i][j]);
        }

        ret.insert(l.get_constraint(TYPE_EQ));
    }

    return ret;
}

MatrixStore* MatrixStore::clone() const {
    // clone this matrix store to obtain a pointer to a new instance
    MatrixStore* ret = new MatrixStore(vars_num, info);
    int i, j;
    for (i = 0; i < vars_num; i++)
        for (j = 0; j < vars_num + 1; j++)
            (*ret)(i, j) = mat[i][j];

    ret->set_consistent(consistent);
    return ret;
}

MatrixStore::~MatrixStore() {
    for (int i = 0; i < vars_num; i++)
        delete[] mat[i];
    if (vars_num > 0)
        delete[] mat;
}
