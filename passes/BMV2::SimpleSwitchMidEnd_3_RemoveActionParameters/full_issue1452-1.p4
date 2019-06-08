control c() {
    bit<32> x;
    bit<32> arg;
    @name("c.b") action b_0() {
        arg = 32w2;
        x = arg;
    }
    apply {
        b_0();
    }
}
control proto();
package top(proto p);
top(c()) main;
