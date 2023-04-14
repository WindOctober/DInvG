
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
 * filename :Rational
 * Author: Sriram Sankaranarayanan  < srirams@theory.stanford.edu>
 * Comments: Rationals
 * Post-Comments: change ints to longs to avoid overflows.
 * Copyright: see README file for copyright information.
 */

#ifndef __RATIONAL__H_
#define __RATIONAL__H_
#include "funcs.h"
#include <iostream>



// A wrapper around the saclib rationals
// This implements rationals. Back in 2002 when I started
// Sting I implemented this library. Even today I regret not
// downloading something off the web. I suck.


// To do: Change the numerator and denominator from int into long or
// else overflows will occur on large complicated examples.

using namespace std;
class Rational{
 private:
  int nu, de;

  void initialize(int n, int d);
  void reduce_to_lowest();

 public:

   Rational(); // the default constructor

   Rational(int n, int d);

   //Rational(RN  t);
   //RN  get_rat () const;

   int num () const{
      return nu;
   }

   int den() const{
      return de;
   }
   

   Rational inv() const;
   Rational & operator=(Rational const &  n);
   Rational & operator=(int n);

   bool operator==(Rational const&  n) const;
   bool operator!=(Rational const& n) const;

   
   bool operator==(int const&  n) const;
   bool operator!=(int const& n) const;

   Rational operator+(Rational const &  n1) const;
   
   Rational operator+( int n1) const;
   
   Rational operator-( Rational const&  n1) const;
   Rational operator-( int n1) const;

   Rational operator* (int n) const;
   Rational operator* (Rational const&  n) const;

   Rational& operator*= (int n) ;
   Rational& operator*= (Rational const&  n);
   
   Rational& operator+=( Rational const&  n1);
   Rational& operator+=( int n1);

   
   Rational& operator-=( Rational const&  n1);
   Rational& operator-=( int n1);
   
   bool operator <(Rational const & p)const;
   bool operator <(int const & n) const;

   bool operator > (Rational const & p) const;
   bool operator > (int const & p) const;

   bool operator >= (Rational const & p) const;
   bool operator >= (int const & p) const;

   bool operator <= (Rational const & p) const;
   bool operator <= (int const & p) const;
   
   
   
   ~Rational();

   bool is_integer() const{
      return den()==1;
   }
   
};

Rational  operator*(int n1, Rational const &  n2);

Rational  operator+(int n1, Rational const &  n2);

ostream & operator<< (ostream & os, Rational const & p1);

#endif
