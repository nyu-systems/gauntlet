control ctrl(out bit<32> c) {
    bit<32> a;
    @name("e") action e() {
        exit;
    }
    apply {
        a = 32w0;
        c = 32w2;
        if (a == 32w0) {
            e();
        } else {
            e();
        }
        c = 32w5;
    }
}
control noop(out bit<32> c);
package p(noop _n);
p(ctrl()) main;
