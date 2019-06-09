#include <core.p4>
parser simple(out bit<2> z);
package m(simple n);
parser p2_0(out bit<2> z2) {
    state start {
        z2 = 2w3 | 2w0 | 2w1 | 2w2;
        transition accept;
    }
}
m(p2_0()) main;
