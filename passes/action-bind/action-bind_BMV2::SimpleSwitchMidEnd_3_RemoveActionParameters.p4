control c(inout bit<32> x) {
    bit<32> b;
    @name("c.a") action a(bit<32> d) {
        b = x;
        b = d;
        x = b;
    }
    @name("c.t") table t_0 {
        actions = {
            a();
        }
        default_action = a(32w0);
    }
    apply {
        t_0.apply();
    }
}
control proto(inout bit<32> x);
package top(proto p);
top(c()) main;
