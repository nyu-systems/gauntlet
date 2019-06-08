control ctrl(out bit<32> c) {
    @name("ctrl.e") action e_0() {
        exit;
    }
    @name("ctrl.t") table t {
        actions = {
            e_0();
        }
        default_action = e_0();
    }
    apply {
        c = 32w2;
        t.apply();
        c = 32w5;
    }
}
control noop(out bit<32> c);
package p(noop _n);
p(ctrl()) main;
