control p(out bit<1> y) {
    bit<1> x_1;
    @name("p.b") action b() {
        y = x_1 & x_1 & (x_1 & x_1) & (x_1 & x_1 & (x_1 & x_1));
    }
    apply {
        x_1 = 1w1;
        b();
    }
}
control simple(out bit<1> y);
package m(simple pipe);
m(p()) main;
