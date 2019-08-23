control ctrl() {
    @name("e") action e() {
        exit;
    }
    @name("f") action f() {
    }
    @name("t") table t {
        actions = {
            e();
            f();
        }
        default_action = e();
    }
    apply {
        switch (t.apply().action_run) {
            e: {
                t.apply();
            }
            f: {
                t.apply();
            }
        }
    }
}
control noop();
package p(noop _n);
p(ctrl()) main;
