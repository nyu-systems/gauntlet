struct S {
    bit<32> x;
}
control c(inout bit<32> b) {
    @name("c.a") action a_0() {
        {
        }
        {
        }
        {
        }
        b = 32w0;
    }
    apply {
        a_0();
    }
}
control proto(inout bit<32> _b);
package top(proto _p);
top(c()) main;
