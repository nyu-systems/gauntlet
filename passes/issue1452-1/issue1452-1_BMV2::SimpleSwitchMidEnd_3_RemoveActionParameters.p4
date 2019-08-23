control c() {
    bit<32> x_0;
    bit<32> arg;
    @name("c.b") action b() {
        arg = 32w2;
        x_0 = arg;
    }
    apply {
        b();
    }
}
control proto();
package top(proto p);
top(c()) main;
