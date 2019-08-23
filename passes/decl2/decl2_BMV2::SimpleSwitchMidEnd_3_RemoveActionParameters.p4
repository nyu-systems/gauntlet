control p() {
    bit<1> z_0;
    bit<1> x_2;
    bit<1> x_3;
    bit<1> y_1;
    bit<1> x;
    bit<1> y;
    @name("p.b") action b() {
        x = x_3;
        x_2 = x;
        z_0 = x & x_2;
        y = z_0;
        y_1 = y;
    }
    apply {
        x_3 = 1w0;
        b();
    }
}
control simple();
package m(simple pipe);
.m(.p()) main;
