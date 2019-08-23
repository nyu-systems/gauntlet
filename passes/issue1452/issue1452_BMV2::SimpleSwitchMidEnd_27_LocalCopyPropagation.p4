control c() {
    bit<32> x_0;
    @name("c.a") action a() {
        x_0 = 32w1;
    }
    apply {
        a();
    }
}
control proto();
package top(proto p);
top(c()) main;
