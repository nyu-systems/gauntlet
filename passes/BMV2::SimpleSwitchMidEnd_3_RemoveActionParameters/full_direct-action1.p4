control c(inout bit<16> y) {
    bit<32> x_0;
    bit<32> arg;
    @name("c.a") action a() {
        arg = x_0;
        y = (bit<16>)arg;
    }
    apply {
        x_0 = 32w10;
        a();
    }
}
control proto(inout bit<16> y);
package top(proto _p);
top(c()) main;
