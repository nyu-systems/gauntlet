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
    bit<16> x_5;
    bool b_2;
    bit<16> x_6;
    bool b_3;
    bit<16> bi;
    bit<16> mb;
    bit<16> bi_1;
    bit<16> mb_1;
    @name("c.a") action a_0() {
        bi = 16w3;
        mb = -bi;
        xv = mb;
    }
    @name("c.a") action a_2() {
        bi_1 = 16w0;
        mb_1 = -bi_1;
        xv = mb_1;
    }
    apply {
        a_0();
        a_2();
        x_5 = xv;
        b_2 = x_5 == 16w0;
        b = b_2;
        xv = x_5;
        x_6 = xv;
        b_3 = x_6 == 16w1;
        xv = x_6;
        b = b_3;
        xv = 16w1;
        x_5 = xv;
        b_2 = x_5 == 16w0;
        xv = x_5;
        b = b_2;
        x_6 = xv;
        b_3 = x_6 == 16w1;
        b = b_3;
        xv = x_6;
    }
}
control ce(out bool b);
parser pe(out bool b);
package top(pe _p, ce _e, @optional ce _e1);
top(_p = par(), _e = c()) main;
