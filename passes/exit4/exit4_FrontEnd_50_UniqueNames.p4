control ctrl() {
    bool tmp;
    @name("e") action e() {
        exit;
    }
    @name("t") table t_0 {
        actions = {
            e();
        }
        default_action = e();
    }
    apply {
        tmp = t_0.apply().hit;
        if (tmp) {
            t_0.apply();
        } else {
            t_0.apply();
        }
    }
}
control noop();
package p(noop _n);
p(ctrl()) main;
