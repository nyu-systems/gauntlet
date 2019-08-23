control c() {
    @name("a") action a() {
    }
    @name("b") action b() {
    }
    @name("t1") table t1 {
        actions = {
            a();
            b();
        }
        default_action = a();
    }
    @name("t2") table t2 {
        actions = {
            a();
        }
        default_action = a();
    }
    apply {
        t1.apply();
        t2.apply();
    }
}
control empty();
package top(empty e);
top(c()) main;
