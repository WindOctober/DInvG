
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
 * filename: Macro.h
 * Author: Hongming Liu<hm-liu@sjtu.edu.cn>
 * Comments: Some macro or define for all files.
 * Copyright: Please see README file.
 */

#ifndef __MACRO__H_
#define __MACRO__H_


#define EXIT_LOCATION "le"

#define TRACE 
#ifndef TRACE
  #define tcout NULL && cout
#else 
  #define tcout cout 
#endif


#endif

