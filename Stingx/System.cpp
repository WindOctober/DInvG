
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

#include "System.h"

#include "myassertions.h"

System::System(var_info* f, var_info* fd, var_info* fr)
    : f_(f),
      fd_(fd),
      fr_(fr),
      n_(f->get_dimension()),
      nd_(fd->get_dimension()),
      r_(fr->get_dimension()),
      context_computed_(false) {}

System::System(System& s, Context& cc)
    : f_(s.get_var_info()),
      fd_(s.get_dual_var_info()),
      fr_(s.get_multiplier_var_info()),
      n_(f_->get_dimension()),
      nd_(fd_->get_dimension()),
      r_(fr_->get_dimension()),
      context_computed_(false) {
    // now obtain location information from context
    get_location_info(s, cc);
    get_transition_info(s, cc);
}

void System::add_location(Location* loc) {
    vloc.push_back(loc);
}

void System::add_transition(TransitionRelation* trans) {
    vtrans.push_back(trans);
}

void System::update_dimensions() {
    n_ = f_->get_dimension();
    nd_ = fd_->get_dimension();
    r_ = fr_->get_dimension();
}

Location const& System::get_location(int index) const {
    PRECONDITION((index >= 0 && index < num_loc()),
                 "System::get_location-- index out of range");
    Location const* ll = vloc[index];
    return (*ll);
}

TransitionRelation const& System::get_transition_relation(int index) const {
    PRECONDITION((index >= 0 && index < num_trans()),
                 "System::get_transition_relation -- index out of range");
    TransitionRelation const* tt = vtrans[index];
    return (*tt);
}


void System::print(ostream& os) const {
    vector<Location*>::const_iterator vi;
    vector<TransitionRelation*>::const_iterator vj;

    os << "System::" << endl;
    os << " =======================================================" << endl;
    os << " System Locations" << endl;

    for (vi = vloc.begin(); vi < vloc.end(); ++vi) {
        os << *(*vi) << endl;
    }

    os << "System Transitions " << endl;

    for (vj = vtrans.begin(); vj < vtrans.end(); ++vj) {
        os << *(*vj) << endl;
    }
}

ostream& operator<<(ostream& os, System const& sys) {
    sys.print(os);
    return os;
}

void System::compute_initial_context() {
    if (context_computed_)
        delete (glc_);

    glc_ = new Context(f_, fd_, fr_);

    vector<Location*>::iterator vi;
    for (vi = vloc.begin(); vi != vloc.end(); ++vi) {
        (*vi)->compute_dual_constraints(*glc_);
    }

    vector<TransitionRelation*>::iterator vj;
    for (vj = vtrans.begin(); vj != vtrans.end(); ++vj) {
        (*vj)->compute_consecution_constraints(*glc_);
    }
}

Context* System::get_context() {
    if (!context_computed_)
        compute_initial_context();

    return glc_;
}

void System::get_location_info(System& s, Context& cc) {
    int nl = s.num_loc();
    int i, j;
    for (i = 0; i < nl; ++i) {
        // obtain a new location
        Location const& lc = s.get_location(i);
        j = lc.get_range_left();
        Location* newl = new Location(n_, f_, fd_, fr_, lc.get_name(), j);

        newl->force_polyset();
        C_Polyhedron& res = newl->get_non_const_poly_reference();

        cc.obtain_primal_polyhedron(j, res);
        add_location(newl);
    }

    // that should do it
}

bool System::location_matches(string name) {
    vector<Location*>::iterator vi;
    for (vi = vloc.begin(); vi != vloc.end(); ++vi) {
        if ((*vi)->matches(name))
            return true;
    }
    return false;
}

Location* System::get_matching_location(string name) {
    vector<Location*>::iterator vi;
    for (vi = vloc.begin(); vi != vloc.end(); ++vi) {
        if ((*vi)->matches(name))
            return (*vi);
    }

    INVARIANT(false, "location not matched.. error.. ");

    return (Location*)0;
}

void System::get_transition_info(System& s, Context& cc) {
    int nt = s.num_trans();
    int i, j, l;

    Location *preloc, *postloc;
    C_Polyhedron* res;
    for (i = 0; i < nt; ++i) {
        TransitionRelation const& tc = s.get_transition_relation(i);
        j = tc.get_mult_index();
        string pre = tc.get_preloc_name();
        string post = tc.get_postloc_name();
        TransitionRelation* newt;
        // 1. obtain matching location.. they better be there
        // 2. compute and set the relation

        if (pre != post) {
            preloc = get_matching_location(pre);
            postloc = get_matching_location(post);

            res = new C_Polyhedron(tc.get_relation());

            newt = new TransitionRelation(n_, f_, fd_, fr_, preloc, postloc,
                                          res, tc.get_name(), j);
            add_transition(newt);
            continue;
        } else if (pre == post) {
            preloc = get_matching_location(pre);
            l = preloc->get_range_left();
            res = new C_Polyhedron(2 * n_);

            if (cc.obtain_transition_relation(j, l, *res) == false) {
                delete (res);
                delete (newt);
                continue;
            }
            newt = new TransitionRelation(n_, f_, fd_, fr_, preloc, preloc, res,
                                          tc.get_name(), j);
            add_transition(newt);
        }
    }
}

void System::add_invariants_and_update(C_Polyhedron& pp, C_Polyhedron& dualp) {
    vector<Location*>::iterator vi;
    for (vi = vloc.begin(); vi != vloc.end(); ++vi) {
        (*vi)->extract_invariants_and_update(pp, dualp);
    }

    return;
}

void System::obtain_trivial_polyhedron(C_Polyhedron& invd) {
    vector<Location*>::iterator vi;
    for (vi = vloc.begin(); vi != vloc.end(); ++vi) {
        (*vi)->add_to_trivial(invd);
    }

    return;
}

void System::do_some_propagation(InvariantMap& im) {
    // iterate through transitions and carry out the propagation steps

    vector<TransitionRelation*>::iterator vi;

    for (vi = vtrans.begin(); vi < vtrans.end(); ++vi) {
        TransitionRelation* tr = (*vi);
        string const& preloc = tr->get_preloc_name();
        string const& postloc = tr->get_postloc_name();

        C_Polyhedron& p1 = im[preloc];
        C_Polyhedron& p2 = im[postloc];

        C_Polyhedron temp(n_, UNIVERSE);

        tr->compute_post_new(&p1, temp);
        p2.poly_hull_assign(temp);
        // done
    }
}

void System::compute_invariant(InvariantMap& im) {
    // compute invariants by cousot halbwachs
    //
    //
    // 1. perform propagation steps
    // 2. perform widening steps
    // print the results
    //

    bool termination = false;

    propagation_time = widening_time = 0;

    while (!termination) {
        InvariantMap im1(im);  // use the copy constructor with trepidation

        // Timer wrap for profiling.

        // Propagation

        Timer prop_timer;
        do_some_propagation(im);  // close im under fwd propagation
        prop_timer.stop();
        propagation_time += prop_timer.compute_time_elapsed();

        // widening
        Timer widening_timer;
        im.BHRZ03_widening_assign(im1);
        widening_timer.stop();
        widening_time += widening_timer.compute_time_elapsed();

        termination = (im.equals(im1));
    }

    cout << "The computed invariant map is " << endl;
    cout << im << endl;
    cout << "Time spent propagating stuff: (0.01s) " << propagation_time
         << endl;
    cout << "Time spent widening stuff: (0.01s)" << widening_time << endl;
    cout << endl << endl;
    return;
}
