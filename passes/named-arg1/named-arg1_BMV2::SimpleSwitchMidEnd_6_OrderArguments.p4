#include <core.p4>
parser par(out bool b) {
    bit<32> x_0;
    state start {
        transition adder_0_start;
    }
    state adder_0_start {
        x_0 = 32w0 + 32w6;
        transition start_0;
    }
    state start_0 {
        b = x_0 == 32w0;
        transition accept;
    }
}
control c(out bool b) {
    bit<16> xv_0;
    bit<16> x_1;
    bool b_0;
    bit<16> x_2;
    bool b_1;
    bit<16> bi;
    bit<16> mb;
    @name("c.a") action a() {
        bi = 16w3;
        mb = -bi;
        xv_0 = mb;
    }
    bit<16> bi_1;
    bit<16> mb_1;
    @name("c.a") action a_2() {
        bi_1 = 16w0;
        mb_1 = -bi_1;
        xv_0 = mb_1;
    }
    apply {
        a();
        a_2();
        x_1 = xv_0;
        b_0 = x_1 == 16w0;
        b = b_0;
        xv_0 = x_1;
        x_2 = xv_0;
        b_1 = x_2 == 16w1;
        xv_0 = x_2;
        b = b_1;
        xv_0 = 16w1;
        x_1 = xv_0;
        b_0 = x_1 == 16w0;
        xv_0 = x_1;
        b = b_0;
        x_2 = xv_0;
        b_1 = x_2 == 16w1;
        b = b_1;
        xv_0 = x_2;
    }
}
control ce(out bool b);
parser pe(out bool b);
package top(pe _p, ce _e, @optional ce _e1);
top(_p = par(), _e = c()) main;
