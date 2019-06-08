control c(inout bit<32> x) {
    bit<32> arg_1;
    @name("c.a") action a_0() {
        arg_1 = 32w10;
        x = arg_1;
    }
    @name("c.t") table t {
        actions = {
            a_0();
        }
        default_action = a_0();
    }
    apply {
        t.apply();
    }
}
control proto(inout bit<32> arg);
package top(proto p);
top(c()) main;
