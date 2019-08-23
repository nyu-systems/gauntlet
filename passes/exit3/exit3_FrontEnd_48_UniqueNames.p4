control ctrl(out bit<32> c) {
    bit<32> a;
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
        a = 32w0;
        c = 32w2;
        if (a == 32w0) {
            t.apply();
        } else {
            t.apply();
        }
        c = 32w5;
    }
}
control noop(out bit<32> c);
package p(noop _n);
p(ctrl()) main;
