control ctrl(out bit<32> c) {
    @name("ctrl.e") action e() {
        exit;
    }
    @name("ctrl.e") action e_2() {
        exit;
    }
    apply {
        c = 32w2;
        if (32w0 == 32w0) 
            e();
        else 
            e_2();
        c = 32w5;
    }
}
control noop(out bit<32> c);
package p(noop _n);
p(ctrl()) main;
