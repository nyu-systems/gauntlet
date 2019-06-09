control c(inout bit<16> y) {
    bit<32> x_0;
    @name("c.a") action a() {
        y = (bit<16>)x_0;
    }
    apply {
        x_0 = 32w10;
        a();
    }
}
control proto(inout bit<16> y);
package top(proto _p);
top(c()) main;
