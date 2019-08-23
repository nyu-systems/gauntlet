control c() {
    @name("a") action a() {
    }
    @name("a") action a_2() {
    }
    @name("b") action b() {
    }
    @name("t1") table t1_0 {
        actions = {
            a();
            b();
        }
        default_action = a();
    }
    @name("t2") table t2_0 {
        actions = {
            a_2();
        }
        default_action = a_2();
    }
    apply {
        t1_0.apply();
        t2_0.apply();
    }
}
control empty();
package top(empty e);
top(c()) main;
