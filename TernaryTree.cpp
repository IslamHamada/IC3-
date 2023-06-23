//
// Created by islam on 21.06.23.
//

#include "TernaryTree.h"

vector<int> TernaryTree::vars;

TernaryTree::TernaryTree(vector<int> vars) {
    this->vars = vars;
}


TernaryTree::TernaryTree() {

}

bool TernaryTree::exists(LitVec cube, size_t& idx) {
    TernaryTree* tree = this;
    int j = 0;
    for(int i = 0; i < vars.size(); i++){
        if(tree == NULL) return false;
        if(cube[j].x / 2 == vars[i]){
            if(cube[j].x % 2 == 0){
                tree = tree->pos;
            } else {
                tree = tree->neg;
            }
            j++;
        } else {
            tree = tree->neu;
        }
    }
    if(tree != NULL) idx = tree->idx;
    return tree != NULL;
}

void TernaryTree::insert(LitVec cube, size_t idx) {
    TernaryTree* tree = this;
    int j = 0;
    for(int i = 0; i < vars.size(); i++){
        if(cube[j].x / 2 == vars[i]){
            if(cube[j].x % 2 == 0){
                if(tree->pos == NULL)
                    tree->pos = new TernaryTree();
                tree = tree->pos;
            } else {
                if(tree->neg == NULL)
                    tree->neg = new TernaryTree();
                tree = tree->neg;
            }
            j++;
        } else {
            if(tree->neu == NULL)
                tree->neu = new TernaryTree();
            tree = tree->neu;
        }
    }
    tree->idx = idx;
}
