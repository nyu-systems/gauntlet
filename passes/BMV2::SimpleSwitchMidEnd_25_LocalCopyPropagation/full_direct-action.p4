control c(inout bit<16> y) {
    bit<32> x;
    @name("c.a") action a_0() {
        y = (bit<16>)x;
    }
    apply {
        x = 32w2;
        a_0();
    }
}
control proto(inout bit<16> y);
package top(proto _p);
top(c()) main;
