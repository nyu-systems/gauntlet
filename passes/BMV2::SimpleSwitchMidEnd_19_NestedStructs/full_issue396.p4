header H {
    bit<32> x;
}
struct S {
    H h;
}
control c(out bool b);
package top(c _c);
control d(out bool b) {
    H h_1;
    H[2] h3;
    H s_h;
    H s1_h;
    bool eout;
    H tmp_0;
    apply {
        h_1.setValid();
        {
            h_1.x = 32w0;
        }
        s_h.setValid();
        s1_h.setValid();
        {
            s1_h.x = 32w0;
        }
        h3[0].setValid();
        h3[1].setValid();
        {
            h3[1].x = 32w1;
        }
        tmp_0.setValid();
        {
            tmp_0.x = 32w0;
        }
        eout = tmp_0.isValid();
        b = h_1.isValid() && eout && h3[1].isValid() && s1_h.isValid();
    }
}
top(d()) main;
