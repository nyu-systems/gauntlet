control c(inout bit<32> x) {
    bit<32> arg_1;
    @name("c.a") action a_0() {
        arg_1 = 32w15;
        x = arg_1;
    }
    apply {
        a_0();
    }
}
control proto(inout bit<32> arg);
package top(proto p);
top(c()) main;
