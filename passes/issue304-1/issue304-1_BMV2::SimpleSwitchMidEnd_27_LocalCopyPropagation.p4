extern X {
    X();
    bit<32> b();
    abstract void a(inout bit<32> arg);
}
control t(inout bit<32> b) {
    @name("t.c1.x") X() c1_x = {
        void a(inout bit<32> arg) {
            bit<32> c1_tmp;
            c1_tmp = this.b();
            arg = arg + c1_tmp;
        }
    };
    @name("t.c2.x") X() c2_x = {
        void a(inout bit<32> arg) {
            bit<32> c2_tmp;
            c2_tmp = this.b();
            arg = arg + c2_tmp;
        }
    };
    apply {
        c1_x.a(b);
        c2_x.a(b);
    }
}
control cs(inout bit<32> arg);
package top(cs _ctrl);
top(t()) main;
