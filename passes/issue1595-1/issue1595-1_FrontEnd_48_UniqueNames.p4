control c(inout bit<32> b) {
    @name("a") action a() {
        b = 32w1;
    }
    @name("t") table t {
        actions = {
            a();
        }
        default_action = a();
    }
    apply {
        switch (t.apply().action_run) {
            a: {
                b[6:3] = 4w1;
            }
        }
    }
}
control empty(inout bit<32> b);
package top(empty _e);
top(c()) main;
