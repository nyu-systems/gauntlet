#include <core.p4>
parser par(out bool b) {
    state start {
        b = false;
        transition accept;
    }
}
control c(out bool b) {
    bit<16> xv_0;
    bool b_1;
    @name("c.a") action a() {
        xv_0 = 16w65533;
    }
    @name("c.a") action a_2() {
        xv_0 = 16w0;
    }
    apply {
        a();
        a_2();
        b = xv_0 == 16w0;
        b_1 = xv_0 == 16w1;
        b = b_1;
        xv_0 = 16w1;
        xv_0 = 16w1;
        b = false;
        b_1 = true;
        b = true;
        xv_0 = 16w1;
    }
}
control ce(out bool b);
parser pe(out bool b);
package top(pe _p, ce _e, @optional ce _e1);
top(_p = par(), _e = c()) main;
