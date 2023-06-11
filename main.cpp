#include <iostream>
#include <string>
#include <time.h>

extern "C" {
#include "aiger/aiger.h"
}

#include "IC3.h"

int main(int argc, char **argv) {
    unsigned int propertyIndex = 0;
    bool basic = false, random = false;
    int verbose = 0;
    string file_name;
    for (int i = 1; i < argc; ++i) {
        if (string(argv[i]) == "-v")
            // option: verbosity
            verbose = 2;
        else if (string(argv[i]) == "-s")
            // option: print statistics
            verbose = max(1, verbose);
        else if (string(argv[i]) == "-r") {
            // option: randomize the run, which is useful in performance
            // testing; default behavior is deterministic
            srand(time(NULL));
            random = true;
        } else if (string(argv[i]) == "-b")
            // option: use basic generalization
            basic = true;
        else
            // optional argument: set property index
//            propertyIndex = (unsigned) atoi(argv[i]);
            file_name = argv[i];
    }

    file_name = "/home/islam/CLionProjects/IC3+/my_smv/counter8_2.aag";
    aiger *aig = aiger_init();
    const char *msg = aiger_open_and_read_from_file(aig, file_name.c_str());

    Model *model = modelFromAiger(aig, propertyIndex);
    aiger_reset(aig);

    bool rv;
    float t1;
    t1 = clock();
    rv = check(*model, verbose, basic, random);
    t1 = (clock() - t1)/ CLOCKS_PER_SEC;
    cout << "result: " << !rv << endl;
    cout << "time: " << t1 << endl;
//    cout << "correctness: " << ic3.correctness() << endl;
    return 0;
}
