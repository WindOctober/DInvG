
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

/*
 * Filename: Context.cc
 * Author: Sriram Sankaranarayanan<srirams@theory.stanford.edu>
 * Comments: The heart of the solver. Was intended to hold the constraint stores
 * and interactively pass constraints.. just grew into this behemoth that cannot
 *           be touched. SACRED CODE. DO NOT MODIFY.
 * Copyright: Please see README file.
 */

#ifndef __CONTEXT__H_
#define __CONTEXT__H_

#include <iostream>
#include <vector>

#include "DisequalityStore.h"
#include "Expression.h"
#include "LinTransform.h"
#include "MatrixStore.h"
#include "PolyStore.h"
#include "SparseLinExpr.h"
#include "Timer.h"
#include "ppl.hh"
#include "var-info.h"

// warning.. this code has too many dead ends to it.
// use with caution.

class Location;
class Clump;
class System;

using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;

class Context {
   private:
    // the main constraint solving ideas are implemented in this class
    // The class contains
    //    1. A Matrix Store for Equality Constraints
    //    2. A Polyhedral Store for the inequalities
    //    3. A Disequality Store for the multipliers
    //    4. A set of expressions that are implicitly ==0
    //    5. A set of expressions that are implicitly >= 0

    MatrixStore* equalStore;
    PolyStore* polyStore;
    DisequalityStore* LambdaStore;
    vector<Expression> *eqExprs, *ineqExprs, *factors;

    Context* childClump;
    var_info *info, *coefInfo, *lambdaInfo;

    int varsNum, coefNum,
        lambdaNum;  // No. of dimensions, coef dimensions, multipliers respectively

    void initialize(var_info* info, var_info* coefInfo, var_info* lambdaInfo);
    void initialize(var_info* info,
                    var_info* coefInfo,
                    var_info* lambdaInfo,
                    MatrixStore* equalStore,
                    PolyStore* polyStore,
                    DisequalityStore* LambdaStore,
                    vector<Expression>* eqExprs,
                    vector<Expression>* ineqExprs);

    void RecursiveSplit(vector<Location*>* locList,
                            C_Polyhedron* dual_poly,
                            int wtime,
                            bool cutoff,
                            Timer& one_timer);
    void Convert_CNF_to_DNF_and_Print(vector<Location*>* locList,
                                      C_Polyhedron* dual_poly,
                                      int wtime,
                                      bool cutoff,
                                      Timer& one_timer);
    bool InConsistency;
    bool leaf;

   public:
    // added by Hongming
    PolyStore* Get_PolyStore() { return (polyStore); }

    // Operations include
    //    1. Creation and Organization of the context
    //       1.1 Initializing the stores
    //       1.2 Adding different types of expressions
    //       1.3 Printing the Stores
    //       1.4 Cloning the content of the stores
    //       1.5 Detecting inconsistencies
    //       1.6 Leaf node detection

    //       1.7 Forming an invariant from a consistent leaf node

    Context(var_info* info, var_info* coefInfo, var_info* lambdaInfo);
    Context(var_info* info,
            var_info* coefInfo,
            var_info* lambdaInfo,
            MatrixStore* equalStore,
            PolyStore* polyStore,
            DisequalityStore* LambdaStore,
            vector<Expression>* eqExprs,
            vector<Expression>* ineqExprs);
    Context(var_info* info,
            var_info* coefInfo,
            var_info* lambdaInfo,
            MatrixStore* equalStore,
            PolyStore* polyStore,
            DisequalityStore* LambdaStore);

    ~Context();

    void addEqExpr(Expression l);
    void addIneqExpr(Expression l);
    void insertMatStore(SparseLinExpr l);
    void insertMatStore(Linear_Expression l);
    void insertPolyStore(
        SparseLinExpr l);  // implicitly assumed to be the expression l > = 0
    void insertPolyStore(Constraint cc);  // Add the constraint directly to
                                            // the polystores polyhedron

    void add_linear_equality(SparseLinExpr l);
    void addTransform(LinTransform l);

    void add_linear_inequality(SparseLinExpr l);
    void addIneqTransform(LinTransform l);

    Context* clone() const;

    void print(ostream& in) const;

    void checkConsistent();
    bool isConsistent();

    // bool is_leaf();

    // void update_invariant(); // Will work only if the node is a leaf without
    // residue

    //    2. Iterated Simplification
    //        2.1 Removing trivial expressions
    //        2.2 Detecting inconsistent stores
    //        2.3 Moving Constraints between stores
    //        2.4 Simplifying expressions

    // Do not call these directly
    void remove_trivial_equalities();  // remove trivial equalities in the store
    void
    remove_trivial_inequalities();  // remove trivial inequalities in the store
    void remove_trivial();          // call this instead to remove the trivial
                                    // expressions in the stores eqExprs and ineqExprs

    // Move linear expressions into the stores

    bool move_constraints_equalities();

    bool move_constraints_inequalities();

    bool move_constraints();  // call this to move the equalities, transforms
                              // and inequalities to the appropriate stores

    void reconcile_stores();

    void simplify_equalities();
    void simplify_inequalities();

    void simplify();

    void simplify_repeat();

    // void apply_linear_transform(LinTransform const & l);

    //    3. Factorization of the expressions and collecting the most frequently
    //       occuring factor for both the equality and the inequality
    //       expressions

    bool checkFactorizable();  // factorize all the equalities and
                                        // return true if something factorizes
    // Also collect expressions that factor in a list

    bool collect_factors_inequalities();  // factorize all the inequalities and
                                          // return true if something factorizes

    // Collect the expressions that factor in a list

    bool checkFactorExists(LinTransform& t);

    Expression&
    getMaxFactor();  // Choose an equality expression that
                                         // factorizes and with maximal number
                                         // of
    // occurrences of its factor.

    //    4. Choosing/Splitting on a factor from the equality
    //       expressions and if no factors then doing the same on the
    //       inequalities

    bool isVisableEquals(
        LinTransform& lt);  // is the transform viable as a proper factor?

    bool splitFactorEquals(
        LinTransform& lt);  // Split into two children contexts if possible

    bool factorizationSplit();  // a cover function to split.
                                            // Returns the number of children
                                            // created  0.. or 2.

    //    5. A special set of strategizing functions that implement
    //      the constraint  solving strategy, handle leaf nodes and
    //      generate the invariants and the residue expressions
    //      The  "generator dropping strategy" is a bad strategy
    //   The to_constraints_ function is not to be used for the time
    //   being.

    void print_children(ostream& os);

    bool is_linear_context();
    // Check if the context has any simplification left to do

    bool is_simplifiable_context();
    // Check if the context is simplifiable

    void RecursiveSplit(System& s, C_Polyhedron* dual_poly);

    void RecursiveSplit(vector<Location*>* locList,
                            C_Polyhedron* dual_poly,
                            int wtime = 1000,
                            bool cutoff = true);
    void Convert_CNF_to_DNF_and_Print(vector<Location*>* locList,
                                      C_Polyhedron* dual_poly,
                                      int wtime = 1000,
                                      bool cutoff = true);
    // A recursive strategy function

    void RecursiveSplit(Clump& clist);
    // A recursive strategy function

    void terminal_strategy(System& s, C_Polyhedron* dual_poly);
    void collect_generators(Generator_System& g);

    void validate_generators(
        Generator_System& g);  // Collect the set of "validated generators in g"

    bool is_valid_generator(Generator const& g);
    int choose_unresolved_multiplier();
    void get_multiplier_counts();
    int get_multiplier_status();

    void splitZeroOneCase(vector<Location*>* locList,
                           C_Polyhedron* dual_poly,
                           int wtime,
                           bool timed,
                           Timer& one_timer);

    void splitZeroOneCase(Clump& clist);

    //
    // From a partial context.. go back to a transition system
    // I will assume ftb that there is just a single location to make things
    // easier
    //

    void obtain_primal_polyhedron(
        int left,
        C_Polyhedron&
            result);  // obtain the primal polyhedron for the initial conditions

    bool is_multiplier_present(int index);

    bool obtain_transition_relation(int mult_index,
                                    int left,
                                    C_Polyhedron& result);

    // collect constraints involving multiplier index in the result
    // as long as those constraints involve only variables from
    // left.. left+varsNum

    bool to_constraints_(int index,
                         int left,
                         C_Polyhedron& result,
                         vector<Expression>* what,
                         bool ineq);
};

ostream& operator<<(ostream& in, Context const& c);
#endif
