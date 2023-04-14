
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
#include "Rational.h"

void Rational::initialize(int n, int d){
  if (d==0) {
    cerr<<"Trying to divide by zero in Rational::initialize"<<endl;
    exit(1);
  }
  nu=n;
  de=d;
  reduce_to_lowest();
}

Rational::Rational(){
   initialize(0,1); 
}

Rational::Rational(int n, int d){
   if (d==0) d=1;
   initialize(n,d);
}

/* Not used anymore
Rational::Rational(RN  what){
   initialize(RNNU(what),RNDE(what));
}

RN  Rational::get_rat() const{
   return r;
}
*/

Rational & Rational::operator=  (Rational const & n){
   initialize(n.num(),n.den());
   return (*this);
}

/* //inlined globally

int Rational::num() const {
  return nu;
}

int Rational::den() const {
  return de;
}

*/


void breakfn(){

}

Rational Rational::inv() const{
   if (nu==0) {
      cerr<<"Rational::inv(): Divide by zero error"<<*this<<endl;
      breakfn();
      exit(1);
   }
   Rational r(den(),num());
   return r;
}

Rational & Rational::operator=(int n){
   initialize(n,1);
   return *this;
}


bool Rational::operator== (Rational const & n) const{
   return num() * n.den()== den() * n.num();
   
   //return (num()==n.num() && den()== n.den()) ||(n.num()==-num() && den()==-n.den());
}


bool Rational::operator!=(Rational const & n) const{
   return num() * n.den()!=den() * n.num();
   //return (num()!=n.num() || den()!= n.den());
}


bool Rational::operator==(int const&  n) const{
   return (num()== n * den());
   //return (num()==n && den()==1)|| (num()==-n && den()==-1) ;
}

bool Rational::operator!=(int const& n) const{
   //reduce_to_lowest();
   return num()!=n*den();
   //return (nu!=n || de !=1);
}


Rational Rational::operator+( Rational const & n1) const{
   Rational tmp(nu * n1.den() + de * n1.num(), n1.den() * de );
   
   tmp.reduce_to_lowest();
   return tmp;
}

Rational Rational::operator+( int n1) const{
  int nu1=n1,de1=1;
  Rational tmp(nu1*de+ nu* de1 , de*de1 );
  return tmp;
}

Rational Rational::operator-( Rational const & n1) const{
  int nu1=n1.num(),de1=n1.den();
  Rational tmp(nu*de1- nu1* de , de*de1 );
   
  return tmp;
}

Rational Rational::operator-( int n1) const{
  Rational tmp(nu - n1 * de  , de );
  return tmp;
}


Rational Rational::operator* (int n) const{
  Rational tmp(nu * n, de);
   return tmp;
}

Rational Rational::operator* (Rational const & n) const{
    Rational tmp(nu * n.num(), de * n.den());
    return tmp;
}

Rational&  Rational::operator*= (int n){
  nu *= n;
  reduce_to_lowest();
  return *this;
}

Rational& Rational::operator*= (Rational const & n){
  nu *= n.num();
  de *= n.den();
  reduce_to_lowest();
   return *this;
}


   
Rational& Rational::operator+=( Rational const & n1){
  int a,b;
  a= nu * n1.den() + n1.num() * de;
  b = de * n1.den();
  nu=a;
  de=b;
  reduce_to_lowest();
  return *this;
}

Rational& Rational::operator+=( int n1){
  nu += n1 * de;
  reduce_to_lowest();
  return *this;
}

   
Rational& Rational::operator-=( Rational const & n1){
  int a,b;
  if (nu==0){
     a=-n1.num();
     b=n1.den();
  } else{
     a= nu * n1.den() - n1.num() * de;
     b = de * n1.den();
  }
  nu=a;
  de=b;
  reduce_to_lowest();
  return *this;
}

Rational& Rational::operator-=( int n1){
   if (nu==0){
      nu=-n1;
      de=1;
   } else{
      nu -= n1 * de;
   }
  reduce_to_lowest();
  return *this;
}


Rational::~Rational(){
   
}

Rational  operator* (int n1, Rational const & n2){
  Rational t (n1 * n2.num(), n2.den());
   return t;
}
Rational  operator+(int n1, Rational const & n2){
   Rational t(n1 * n2.den()+ n2.num(),n2.den() );
   return t;
}

Rational  operator-(int n1, Rational const & n2){
   Rational t( n1 * n2.den()- n2.num(),n2.den() );
   return t;
}

ostream & operator<< (ostream & os, Rational const & p1){
   
   int n= p1.num(), d= p1.den();
   if (d==1)
      os<< n;
   else
      os<< n <<"/"<<d<<" ";
   return os;
}

void Rational::reduce_to_lowest(){
   bool sgn=((nu<0 && de >0) ||( de <0 && nu >0));
   if (nu<0)
      nu=-nu;
   if (de<0)
      de=-de;
   
  int g = gcd(nu,de);

  if (g==0){ // nu must be zero then
     if (nu!=0) {
        cerr<<"Rational::reduce_to_lowest -- Fatal Error in result num="<<nu<<" den="<<de<<endl;
        exit(1);
     }

     de=1;
     return;
  }
  nu/=g;
  de/=g;
  
  if (sgn){  
        nu=-nu;
     }

}

bool Rational::operator <(Rational const & p)const{
   
   return (nu*p.den()<de*p.num());
}

bool Rational::operator <(int const & n) const{
     return (nu <de * n);
}



bool Rational::operator >(Rational const & p)const{
   
   return (nu*p.den() > de*p.num());
}

bool Rational::operator >(int const & n) const{
     return (nu  > de * n);
}


bool Rational::operator >=(Rational const & p)const{
   
   return (nu*p.den() >= de*p.num());
}

bool Rational::operator >=(int const & n) const{
     return (nu  >= de * n);
}


bool Rational::operator <=(Rational const & p)const{
   
   return (nu*p.den() <= de*p.num());
}

bool Rational::operator <=(int const & n) const{
     return (nu  <= de * n);
}


