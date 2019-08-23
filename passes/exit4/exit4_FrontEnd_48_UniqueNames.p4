control ctrl() {
    bool tmp_0;
    @name("e") action e() {
        exit;
    }
    @name("t") table t {
        actions = {
            e();
        }
        default_action = e();
    }
    apply {
        tmp_0 = t.apply().hit;
        if (tmp_0) {
            t.apply();
        } else {
            t.apply();
        }
    }
}
control noop();
package p(noop _n);
p(ctrl()) main;
