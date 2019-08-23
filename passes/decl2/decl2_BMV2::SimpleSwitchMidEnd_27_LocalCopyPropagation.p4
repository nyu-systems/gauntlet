control p() {
    bit<1> x_3;
    @name("p.b") action b() {
    }
    apply {
        x_3 = 1w0;
        b();
    }
}
control simple();
package m(simple pipe);
.m(.p()) main;
