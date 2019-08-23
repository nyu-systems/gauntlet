header H {
    bit<32>    a;
    varbit<32> b;
}
struct S {
    bit<32> a;
    H       h;
}
control c(out bit<1> x) {
    varbit<32> a_0;
    varbit<32> b_0;
    H h1_0;
    H h2_0;
    S s1_0;
    S s2_0;
    H[2] a1_0;
    H[2] a2_0;
    apply {
        if (a_0 == b_0) {
            x = 1w1;
        } else if (!h1_0.isValid() && !h2_0.isValid() || h1_0.isValid() && h2_0.isValid() && h1_0.a == h2_0.a && h1_0.b == h2_0.b) {
            x = 1w1;
        } else if (true && s1_0.a == s2_0.a && (!s1_0.h.isValid() && !s2_0.h.isValid() || s1_0.h.isValid() && s2_0.h.isValid() && s1_0.h.a == s2_0.h.a && s1_0.h.b == s2_0.h.b)) {
            x = 1w1;
        } else if (true && (!a1_0[0].isValid() && !a2_0[0].isValid() || a1_0[0].isValid() && a2_0[0].isValid() && a1_0[0].a == a2_0[0].a && a1_0[0].b == a2_0[0].b) && (!a1_0[1].isValid() && !a2_0[1].isValid() || a1_0[1].isValid() && a2_0[1].isValid() && a1_0[1].a == a2_0[1].a && a1_0[1].b == a2_0[1].b)) {
            x = 1w1;
        } else {
            x = 1w0;
        }
    }
}
control ctrl(out bit<1> x);
package top(ctrl _c);
top(c()) main;
