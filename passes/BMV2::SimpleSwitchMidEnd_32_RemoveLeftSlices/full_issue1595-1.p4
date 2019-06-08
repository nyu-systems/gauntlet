control c(inout bit<32> b) {
    @name("c.a") action a_0() {
    }
    @name("c.t") table t {
        actions = {
            a_0();
        }
        default_action = a_0();
    }
    apply {
        switch (t.apply().action_run) {
            a_0: {
                b = b & ~32w0x78 | (bit<32>)4w1 << 3 & 32w0x78;
            }
        }
    }
}
control empty(inout bit<32> b);
package top(empty _e);
top(c()) main;
