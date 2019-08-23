#include <core.p4>
parser par(out bool b) {
    bit<32> x;
    state start {
        transition adder_0_start;
    }
    state adder_0_start {
        x = 32w0 + 32w6;
        transition start_0;
    }
    state start_0 {
        b = x == 32w0;
        transition accept;
    }
}
control c(out bool b) {
    bit<16> xv;
    bit<16> x_3;
    bool b_2;
    bit<16> x_4;
    bool b_3;
    @name("a") action a_0(in bit<16> bi_0, out bit<16> mb_0) {
        mb_0 = -bi_0;
    }
    @name("a") action a_1(in bit<16> bi_0, out bit<16> mb_0) {
        mb_0 = -bi_0;
    }
    apply {
        a_0(bi_0 = 16w3, mb_0 = xv);
        a_1(mb_0 = xv, bi_0 = 16w0);
        x_3 = xv;
        b_2 = x_3 == 16w0;
        b = b_2;
        xv = x_3;
        x_4 = xv;
        b_3 = x_4 == 16w1;
        xv = x_4;
        b = b_3;
        xv = 16w1;
        x_3 = xv;
        b_2 = x_3 == 16w0;
        xv = x_3;
        b = b_2;
        x_4 = xv;
        b_3 = x_4 == 16w1;
        b = b_3;
        xv = x_4;
    }
}
control ce(out bool b);
parser pe(out bool b);
package top(pe _p, ce _e, @optional ce _e1);
top(_e = c(), _p = par()) main;
