control p(out bit<1> y) {
    bit<1> x_3;
    @name("p.b") action b_0() {
        y = x_3 & x_3 & (x_3 & x_3) & (x_3 & x_3 & (x_3 & x_3));
    }
    apply {
        x_3 = 1w1;
        b_0();
    }
}
control simple(out bit<1> y);
package m(simple pipe);
m(p()) main;
