
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

#ifndef D__MY_ASSERTIONS__H_
#define D__MY_ASSERTIONS__H_


#define ASSERTMSG(TST,MSG)					\
		( (TST) ? (void)0				\
			: (cerr << __FILE__ "(" << __LINE__	\
				<< "): Assertion failed " #TST	\
				<< MSG << endl << endl,abort()))

#define PRECONDITION(TST,MSG) ASSERTMSG(TST,"Precondition " << MSG)


#ifndef NDEBUG

#  define DEBUG_INFO(MSG)  (cerr << __FILE__ "(" << __LINE__	\
				<< "):"	\
				<< MSG << endl)

#  define POSTCONDITION(TST,MSG) ASSERTMSG(TST,"Postcondition " << MSG)
#  define INVARIANT(TST,MSG) ASSERTMSG(TST,"Invariant " << MSG)

#else

#  define DEBUG_INFO(MSG) ((void) 0)
#  define POSTCONDITION(TST,MSG) ((void)0)
#  define INVARIANT(TST,MSG) ((void)0)

#endif

#define UNREACHABLE(MSG) INVARIANT( (false), MSG);

// Just testing to see if the linking thing works

#endif
