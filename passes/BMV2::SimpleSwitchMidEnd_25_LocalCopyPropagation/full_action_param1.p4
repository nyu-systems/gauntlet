control c(inout bit<32> x) {
    @name("c.a") action a_0() {
        x = 32w15;
    }
    apply {
        a_0();
    }
}
control proto(inout bit<32> arg);
package top(proto p);
top(c()) main;
