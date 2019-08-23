control c() {
    bit<32> x;
    @name("b") action b(out bit<32> arg_0) {
        arg_0 = 32w2;
    }
    apply {
        b(x);
    }
}
control proto();
package top(proto p);
top(c()) main;
