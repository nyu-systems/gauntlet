control ctrl(out bit<32> c) {
    @name("ctrl.e") action e_0() {
        exit;
    }
    @name("ctrl.e") action e_2() {
        exit;
    }
    apply {
        c = 32w2;
        if (32w0 == 32w0) 
            e_0();
        else 
            e_2();
        c = 32w5;
    }
}
control noop(out bit<32> c);
package p(noop _n);
p(ctrl()) main;
