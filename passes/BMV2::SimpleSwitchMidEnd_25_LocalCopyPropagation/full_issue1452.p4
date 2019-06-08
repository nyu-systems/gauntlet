control c() {
    bit<32> x;
    @name("c.a") action a_0() {
        x = 32w1;
    }
    apply {
        a_0();
    }
}
control proto();
package top(proto p);
top(c()) main;
