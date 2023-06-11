/*********************************************************************
Copyright (c) 2013, Aaron Bradley

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#ifndef IC3_h_INCLUDED
#define IC3_h_INCLUDED

#include "Model.h"

//namespace IC3 {

struct State {
    size_t successor;  // successor State
    LitVec latches;
    LitVec inputs;
    size_t index;      // for pool
    bool used;         // for pool
};

// A CubeSet is a set of ordered (by integer value) vectors of
// Minisat::Lits.
static bool _LitVecComp(const LitVec &v1, const LitVec &v2) {
    if (v1.size() < v2.size()) return true;
    if (v1.size() > v2.size()) return false;
    for (size_t i = 0; i < v1.size(); ++i) {
        if (v1[i] < v2[i]) return true;
        if (v2[i] < v1[i]) return false;
    }
    return false;
}

static bool _LitVecEq(const LitVec &v1, const LitVec &v2) {
    if (v1.size() != v2.size()) return false;
    for (size_t i = 0; i < v1.size(); ++i)
        if (v1[i] != v2[i]) return false;
    return true;
}

class LitVecComp {
public:
    bool operator()(const LitVec &v1, const LitVec &v2) {
        return _LitVecComp(v1, v2);
    }
};

// A proof obligation.
struct Obligation {
    Obligation(size_t st, size_t l, size_t d) :
            state(st), level(l), depth(d) {}

    size_t state;  // Generalize this state...
    size_t level;  // ... relative to this level.
    size_t depth;  // Length of CTI suffix to error.
};

class ObligationComp {
public:
    bool operator()(const Obligation &o1, const Obligation &o2) {
        if (o1.level < o2.level) return true;  // prefer lower levels (required)
        if (o1.level > o2.level) return false;
        if (o1.depth < o2.depth) return true;  // prefer shallower (heuristic)
        if (o1.depth > o2.depth) return false;
        if (o1.state < o2.state) return true;  // canonical final decider
        return false;
    }
};

typedef set<Obligation, ObligationComp> PriorityQueue;
typedef Minisat::vec<Minisat::Lit> MSLitVec;
typedef set<LitVec, LitVecComp> CubeSet;

struct idxLitVec{
    LitVec cube;
    size_t idx;
};

class idxLitVecComp {
public:
    bool operator()(const idxLitVec &v1, const idxLitVec &v2) {
        return _LitVecComp(v1.cube, v2.cube);
    }
};

typedef set<idxLitVec, idxLitVecComp> idxCubeSet;

struct Frame {
    size_t k;             // steps from initial state
    CubeSet borderCubes;  // additional cubes in this and previous frames
    Minisat::Solver *consecution;
};


class IC3 {
public:
    IC3(Model &_model);

    ~IC3();

    bool check();

    void printWitness();

    string stringOfLitVec(const LitVec &vec);

    State &state(size_t sti);

    size_t newState();

    void delState(size_t sti);

    void resetStates();

    void extend();

    Model &model;
    size_t k;
    vector<State> states;
    size_t nextState;


    vector<Frame> frames;

    Minisat::Solver *lifts;
    Minisat::Lit notInvConstraints;

    float numLits, numUpdates;

    void updateLitOrder(const LitVec &cube, size_t level);

    void orderCube(LitVec &cube);

    void orderAssumps(MSLitVec &cube, bool rev, int start = 0);

    size_t stateOf(Frame &fr, size_t succ = 0, LitVec *succ_cube = NULL);

    bool initiation(const LitVec &latches);

    bool consecution(size_t fi, const LitVec &latches, size_t succ = 0,
                     LitVec *core = NULL, size_t *pred = NULL,
                     bool orderedCore = false);

    size_t maxDepth, maxCTGs, maxJoins, micAttempts;

    bool ctgDown(size_t level, LitVec &cube, size_t keepTo, size_t recDepth);

    void mic(size_t level, LitVec &cube, size_t recDepth);

    void mic(size_t level, LitVec &cube);

    size_t earliest;  // track earliest modified level in a major iteration

    void addCube(size_t level, LitVec &cube, bool toAll = true,
                 bool silent = false);

    size_t generalize(size_t level, LitVec cube);

    bool handleObligations(PriorityQueue obls);

    bool trivial;  // indicates whether strengthening was required

    bool strengthen();

    bool propagate();

    int verbose; // 0: silent, 1: stats, 2: all
    bool random;

    size_t cexState;

    int nQuery, nCTI, nCTG, nmic;
    clock_t startTime, satTime;
    int nCoreReduced, nAbortJoin, nAbortMic;

    clock_t time();

    clock_t timer;

    void startTimer();

    void endTimer(clock_t &t);

    void printStats();

    friend bool check(Model &, int, bool, bool);

    struct HeuristicLitOrder {
        HeuristicLitOrder() : _mini(1 << 20) {}

        vector<float> counts;
        size_t _mini;

        void count(const LitVec &cube) {
            assert (!cube.empty());
            // assumes cube is ordered
            size_t sz = (size_t) Minisat::toInt(Minisat::var(cube.back()));
            if (sz >= counts.size()) counts.resize(sz + 1);
            _mini = (size_t) Minisat::toInt(Minisat::var(cube[0]));
            for (LitVec::const_iterator i = cube.begin(); i != cube.end(); ++i)
                counts[(size_t) Minisat::toInt(Minisat::var(*i))] += 1;
        }

        void decay() {
            for (size_t i = _mini; i < counts.size(); ++i)
                counts[i] *= 0.99;
        }
    } litOrder;

    struct SlimLitOrder {
        HeuristicLitOrder *heuristicLitOrder;

        SlimLitOrder() {}

        bool operator()(const Minisat::Lit &l1, const Minisat::Lit &l2) const {
            // l1, l2 must be unprimed
            size_t i2 = (size_t) Minisat::toInt(Minisat::var(l2));
            if (i2 >= heuristicLitOrder->counts.size()) return false;
            size_t i1 = (size_t) Minisat::toInt(Minisat::var(l1));
            if (i1 >= heuristicLitOrder->counts.size()) return true;
            return (heuristicLitOrder->counts[i1] < heuristicLitOrder->counts[i2]);
        }
    } slimLitOrder;

    idxCubeSet extra_bad_states;

    bool strengthen_extra(size_t frame_idx);

    void add_extra_bad_state(idxLitVec idxCube);
};

bool check(Model &model,
           int verbose = 0,       // 0: silent, 1: stats, 2: informative
           bool basic = false,    // simple inductive generalization
           bool random = false);  // random runs for statistical profiling

static void print_var(int v, VarVec vars) {
//        cout << "(" << vars[v].name() << "," << vars[v].index() << "," << v << ")" << ", ";
    cout << vars[v].name() << ", ";
}

static void print_lit(Minisat::Lit &l, VarVec vars) {
    if (Minisat::sign(l)) {
        cout << "!";
    }
    print_var(var(l), vars);
}

static void print_cube(LitVec s, VarVec vars) {
    cout << "{";
    for (Minisat::Lit l: s) {
        print_lit(l, vars);
    }
    cout << "}";
    cout << endl;
}

static void print_cube_n(LitVec s, VarVec vars) {
    cout << "{";
    for (Minisat::Lit l: s) {
        Minisat::Lit l2 = ~l;
        print_lit(l2, vars);
    }
    cout << "}";
    cout << endl;
}

static void print_frame(Frame f, VarVec vars) {
    cout << "\t";
    cout << "Frame index: " << f.k << endl;
    CubeSet cs = f.borderCubes;
    for (LitVec c: cs) {
        cout << "\t";
        print_cube(c, vars);
    }
    cout << endl << endl;
}

static void print_frames(vector<Frame> f, VarVec vars) {
    for (int i = 0; i < f.size(); i++) {
        Frame x = f[i];
        print_frame(x, vars);
    }
    cout << "<<<<<<<<<<<<<<<<<<<<<<<<<" << endl;
}

static void print_vec_lit(MSLitVec &s) {
    cout << "{";
    for (int i = 0; i < s.size(); i++) {
        cout << toInt(s[i]) << ", ";
    }
    cout << "}";
    cout << endl;
}
//}

#endif
