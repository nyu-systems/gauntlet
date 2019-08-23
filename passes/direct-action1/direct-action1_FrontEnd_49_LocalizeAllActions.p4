control c(inout bit<16> y) {
    bit<32> x;
    @name("a") action a_0(bit<32> arg_0) {
        y = (bit<16>)arg_0;
    }
    apply {
        x = 32w10;
        a_0(x);
    }
}
control proto(inout bit<16> y);
package top(proto _p);
top(c()) main;
