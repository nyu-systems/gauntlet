control c() {
    @name(".Global") action Global_1() {
    }
    @name("t") table t {
        actions = {
            Global_1();
        }
        default_action = Global_1();
    }
    apply {
        t.apply();
    }
}
control none();
package top(none n);
top(c()) main;
