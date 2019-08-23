control c(inout bit<32> x) {
    @name("a") action a(inout bit<32> b_0, bit<32> d) {
        b_0 = d;
    }
    @name("t") table t {
        actions = {
            a(x);
        }
        default_action = a(x, 32w0);
    }
    apply {
        t.apply();
    }
}
control proto(inout bit<32> x);
package top(proto p);
top(c()) main;
