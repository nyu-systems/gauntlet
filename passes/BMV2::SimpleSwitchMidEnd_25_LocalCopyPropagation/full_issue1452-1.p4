control c() {
    @name("c.b") action b_0() {
    }
    apply {
        b_0();
    }
}
control proto();
package top(proto p);
top(c()) main;
