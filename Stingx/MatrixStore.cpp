
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
    varsNum = 0;
    return;
}
void MatrixStore::initialize(int varsNum, var_info* info) {
    this->varsNum = varsNum;
    mat = new Rational*[varsNum];  // the last column is the $b$ augment
    for (int i = 0; i < varsNum; i++)
        mat[i] = new Rational[varsNum + 1];

    zero_out();
    this->info = info;
    consistent = true;
}

MatrixStore::MatrixStore(int varsNum, var_info* info) {
    initialize(varsNum, info);
}

void MatrixStore::zero_out() {
    for (int i = 0; i < varsNum; i++)
        for (int j = 0; j < varsNum + 1; j++)
            mat[i][j] = 0;
    consistent = true;
}

void MatrixStore::init_set(int varsNum, var_info* coefInfo) {
    initialize(varsNum, coefInfo);
}

int MatrixStore::simplify(SparseLinExpr& expression) const {
    // Use the guassian elimination type technique
    int i, j;
    int lead = varsNum + 1;
    Rational temp1, temp2;
    for (i = 0; i < varsNum; i++) {
        if (!(mat[i][i] == 0)) {
            if (expression(i) != 0) {
                // Perform a reduction of the expression
                for (j = 0; j < i; j++) {
                    temp2 = (expression(i) * mat[i][j]) * mat[i][i].inverse();
                    expression.subtract_coefficient(j, temp2);
                }
                for (j = i + 1; j < varsNum + 1; j++) {
                    temp2 = (expression(i) * mat[i][j]) * mat[i][i].inverse();
                    expression.subtract_coefficient(j, temp2);
                }
                expression.setCoefficient(i, 0);  // reset expression[i]
            }
        }
    }

    for (i = 0; i < varsNum + 1; i++) {
        if (expression(i) != 0) {
            lead = i;
            break;
        }
    }

    return lead;
}

void MatrixStore::back_substitute(int lead) {
    if (lead >= varsNum || mat[lead][lead] == 0)
        return;
    Rational temp1, temp2;
    int i, j;
    for (i = lead - 1; i >= 0; i--) {
        if (mat[i][lead] != 0) {
            for (j = lead + 1; j < varsNum + 1; j++) {
                temp1 = mat[i][j];
                temp2 =
                    mat[lead][j] * mat[i][lead] * (mat[lead][lead].inverse());
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

    if (lead >= varsNum) {
        if (expression(varsNum) != 0) {
            consistent = false;
            return false;
        } else
            return true;  // Nothing to be done for the constraint
    }

    // else copy the constraint to the lead row

    for (i = lead; i < varsNum + 1; i++)
        mat[lead][i] = expression(i);
    back_substitute(lead);
    return true;
}

bool MatrixStore::isConsistent() const {
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
    for (i = 0; i < varsNum; i++) {
        if (mat[i][i] == 0)
            continue;
        some = true;
        cout << mat[i][i] << " * " << info->getName(i);
        for (j = i + 1; j < varsNum; j++) {
            if (mat[i][j] == 0)
                continue;
            cout << "+" << mat[i][j] << " * " << info->getName(j);
        }

        if (mat[i][varsNum] != 0) {
            cout << " + " << mat[i][varsNum];
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
    int varsNum = p.getDim();

    var_info* info = p.getInfo();
    Rational** mat = p.get_matrix();

    if (!p.isConsistent())
        cout << "Inconsistent" << endl;

    for (i = 0; i < varsNum; i++) {
        if (mat[i][i] == 0)
            continue;
        some = true;
        os << "├ ";
        os << mat[i][i] << " * " << info->getName(i);
        for (j = i + 1; j < varsNum; j++) {
            if (mat[i][j] == 0)
                continue;
            os << "+" << mat[i][j] << " * " << info->getName(j);
        }
        if (mat[i][varsNum] != 0) {
            os << " + " << mat[i][varsNum];
        }
        os << " = 0" << endl;
    }
    if (!some) {
        os << "├ ";
        os << "Empty Store" << endl;
    }

    return os;
}

int MatrixStore::getDim() const {
    return varsNum;
}
var_info* MatrixStore::getInfo() const {
    return info;
}

Rational** MatrixStore::get_matrix() const {
    return mat;
}

Constraint_System MatrixStore::to_constraint_system() const {
    SparseLinExpr l(varsNum, info);
    int i, j;
    Constraint_System ret;
    for (i = 0; i < varsNum; i++) {
        l.setCoefficient(varsNum, mat[i][varsNum]);
        for (j = 0; j < varsNum; j++) {
            l.setCoefficient(j, mat[i][j]);
        }

        ret.insert(l.get_constraint(TYPE_EQ));
    }

    return ret;
}

MatrixStore* MatrixStore::clone() const {
    // clone this matrix store to obtain a pointer to a new instance
    MatrixStore* ret = new MatrixStore(varsNum, info);
    int i, j;
    for (i = 0; i < varsNum; i++)
        for (j = 0; j < varsNum + 1; j++)
            (*ret)(i, j) = mat[i][j];

    ret->set_consistent(consistent);
    return ret;
}

MatrixStore::~MatrixStore() {
    for (int i = 0; i < varsNum; i++)
        delete[] mat[i];
    if (varsNum > 0)
        delete[] mat;
}
