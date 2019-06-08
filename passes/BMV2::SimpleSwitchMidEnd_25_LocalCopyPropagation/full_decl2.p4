control p() {
    bit<1> x_1;
    @name("p.b") action b_0() {
    }
    apply {
        x_1 = 1w0;
        b_0();
    }
}
control simple();
package m(simple pipe);
.m(.p()) main;
