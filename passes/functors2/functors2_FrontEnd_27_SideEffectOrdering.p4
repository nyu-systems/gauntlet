#include <core.p4>
parser p1(out bit<2> z1)(bit<2> a) {
    state start {
        {
            z1 = a;
        }
        transition accept;
    }
}
parser p2(out bit<2> z2)(bit<2> b, bit<2> c) {
    bit<2> x1_0;
    bit<2> x2_0;
    bit<2> x3_0;
    @name("p1a") p1(2w0) p1a_0;
    @name("p1b") p1(b) p1b_0;
    @name("p1c") p1(c) p1c_0;
    state start {
        {
            p1a_0.apply(x1_0);
        }
        {
            p1b_0.apply(x2_0);
        }
        {
            p1c_0.apply(x3_0);
        }
        {
            z2 = b | c | x1_0 | x2_0 | x3_0;
        }
        transition accept;
    }
}
parser simple(out bit<2> z);
package m(simple n);
m(p2(2w1, 2w2)) main;
