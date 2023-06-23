//
// Created by islam on 21.06.23.
//

#include <minisat/core/SolverTypes.h>
#include "vector"
//#include "Model.h"

#ifndef IC3_TERNARYTREE_H
#define IC3_TERNARYTREE_H

#endif //IC3_TERNARYTREE_H

using namespace std;

typedef vector<Minisat::Lit> LitVec;

class TernaryTree{
public:
    static vector<int> vars;
    TernaryTree* neg = NULL;
    TernaryTree* pos = NULL;
    TernaryTree* neu = NULL;
    LitVec* cube;
    size_t idx;
//    int depth;
//public:
    TernaryTree();
    TernaryTree(vector<int> vars);
    void insert(LitVec cube, size_t idx);
    bool exists(LitVec cube, size_t& idx);
};

//vector<int> TernaryTree::vars = {};