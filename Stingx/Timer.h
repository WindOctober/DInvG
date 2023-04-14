
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
 * filename: Timer
 * Author: Sriram Sankaranarayanan
 * Comments: Stop watch timer for profiling code. Uses real-time. Please be careful. Parallel processes
 *         will report more time. Ideal for dual processor machines.. I think.
 * Post-comments: Too complicated for what I really need in this release of the implementation. But I will just use it.
 * Copyright: see README file.
 */

#ifndef __TIMER__H_
#define __TIMER__H_


using namespace std;


class Timer{
   
   // implement a rough stop watch capacity to start, stop and freeze. 
   // This could of course measure the amount of time doing different things
   // Alarm timers are not being used in this implementation.
   
 private:
  long int start_time; // when did  I start
  long int time_elapsed; // in clock ticks
  long int nclticks; // how many clockticks maketh a second
  
  long int time_alarmed; // the amount of time I am alarmed

  // state variables for the timer.
  
  bool alarm; // Is this an alarm timer with a time_up or simply a timer for computing time elapsed?
  bool time_up; // has the timer gone off
  bool running; // is the timer running .. ie parameters set
  bool frozen; // if the timer is running, has it been frozen?
  
  void initialize(bool frozen, int time_alarmed);
  
 public:
  
  Timer(); // start the timer .. no alarm
  Timer(int time_alarmed); // the amount of time in mS
  
  void start(int how_much );

  void stop(); // stop the timer

  long int compute_time_elapsed();
  
  void restart(); // restart the timer
  bool is_time_up(); // is the time up
  
}; 
#endif

