#include <core.p4>
parser par(out bool b) {
    bit<32> x;
    bit<32> y;
    bit<32> x_4;
    state start {
        y = 32w0;
        x_4 = y + 32w6;
        x = x_4;
        b = x == 32w0;
        transition accept;
    }
}
control c(out bool b) {
    bit<16> xv;
    bool b_3;
    @name("c.a") action a_0() {
        xv = -16w3;
    }
    @name("c.a") action a_2() {
        xv = -16w0;
    }
    apply {
        a_0();
        a_2();
        b = xv == 16w0;
        b_3 = xv == 16w1;
        b = b_3;
        xv = 16w1;
        xv = 16w1;
        b = 16w1 == 16w0;
        b_3 = 16w1 == 16w1;
        b = 16w1 == 16w1;
        xv = 16w1;
    }
}
control ce(out bool b);
parser pe(out bool b);
package top(pe _p, ce _e, @optional ce _e1);
top(_p = par(), _e = c()) main;
