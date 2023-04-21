
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

#include "Timer.h"

#include <sys/times.h>
#include <unistd.h>

#include <iostream>
using namespace std;

#define SOMETHING_LONG 10000

void Timer::initialize(bool alarm, int time_alarmed)
{
    nclticks = sysconf(_SC_CLK_TCK);  // the number of clock ticks per second

    if (alarm) {
        this->running = true;
        alarm = true;
        this->frozen = false;
        this->time_up = (time_alarmed < 0);

        // now obtain the start time
        struct tms buf;
        times(&buf);
        start_time = buf.tms_utime;

        // now set the remaining parameters
        time_elapsed = 0;
        this->time_alarmed = (long)((time_alarmed * nclticks) / 1000);
    }
    else {
        this->running = true;

        this->alarm = false;
        this->frozen = this->time_up = false;
        time_elapsed = 0;
        struct tms buf;
        times(&buf);
        start_time = buf.tms_utime;
        // now set the remaining parameters

        time_elapsed = 0;
        time_alarmed = SOMETHING_LONG;
        this->time_alarmed = (long)((time_alarmed * nclticks) / 1000);
    }
}

Timer::Timer()
{
    initialize(false,
               SOMETHING_LONG);  // some dummy parameter for time alarmed.
}

Timer::Timer(int how_much)
{
    initialize(true,
               how_much);  // Timer object constructed with the clock ticking
}

void Timer::start(int how_much)
{
    initialize(true, how_much);  // timer now actually initialized
}

long int Timer::compute_time_elapsed()
{
    if (!alarm && !running) return time_elapsed;

    struct tms buf;
    times(&buf);

    time_elapsed = ((long int)buf.tms_utime - start_time);

    return time_elapsed;
}

void Timer::stop()
{
    if (!alarm) {
        if (running) {
            compute_time_elapsed();
            running = false;
        }
        return;
    }

    if (!running || frozen || time_up) return;

    // if time is not up yet
    // 1. compute the time elapsed
    // 2. subtract from the time_alarmed, and reset time_elapsed
    // 3. set frozen if time is not already up

    compute_time_elapsed();

    time_alarmed -= time_elapsed;
    time_elapsed = 0;

    if (time_alarmed <= 0)
        time_up = true;
    else
        frozen = true;
}

void Timer::restart()
{
    if (!alarm) {
        initialize(false, SOMETHING_LONG);
        return;
    }

    // if not frozen or not running or time is up return
    // 1. reset start_time to  the current time
    // 2. set time_elapsed to zero
    // 3. reset frozen

    if (!frozen || !running || time_up) {
        return;
    }

    struct tms buf;
    times(&buf);

    start_time = buf.tms_utime;

    time_elapsed = 0;
    time_up = (time_alarmed > 0);
    running = true;
    frozen = false;
    // that does it
    return;
}

bool Timer::is_time_up()
{
    // if time is already up then say yes
    // else if not running or frozen then say no
    // else
    //  1. recompute time_elapsed
    if (!alarm) return false;

    if (time_up) return true;
    if (!running || frozen) return false;
    compute_time_elapsed();

    if (time_elapsed >= time_alarmed)
        time_up = true;
    else
        time_up = false;

    return time_up;
}
