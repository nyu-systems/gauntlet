header H {
    bit<32>    a;
    varbit<32> b;
}
struct S {
    bit<32> a;
    H       h;
}
control c(out bit<1> x) {
    varbit<32> a_1;
    varbit<32> b_1;
    H h1;
    H h2;
    S s1;
    S s2;
    H[2] a1;
    H[2] a2;
    apply {
        if (a_1 == b_1) 
            x = 1w1;
        else 
            if (!h1.isValid() && !h2.isValid() || h1.isValid() && h2.isValid() && h1.a == h2.a && h1.b == h2.b) 
                x = 1w1;
            else 
                if (true && s1.a == s2.a && (!s1.h.isValid() && !s2.h.isValid() || s1.h.isValid() && s2.h.isValid() && s1.h.a == s2.h.a && s1.h.b == s2.h.b)) 
                    x = 1w1;
                else 
                    if (true && (!a1[0].isValid() && !a2[0].isValid() || a1[0].isValid() && a2[0].isValid() && a1[0].a == a2[0].a && a1[0].b == a2[0].b) && (!a1[1].isValid() && !a2[1].isValid() || a1[1].isValid() && a2[1].isValid() && a1[1].a == a2[1].a && a1[1].b == a2[1].b)) 
                        x = 1w1;
                    else 
                        x = 1w0;
    }
}
control ctrl(out bit<1> x);
package top(ctrl _c);
top(c()) main;
