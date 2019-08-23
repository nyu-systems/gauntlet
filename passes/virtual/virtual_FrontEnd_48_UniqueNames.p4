struct data {
    bit<16> a;
    bit<16> b;
}
extern Virtual {
    Virtual();
    abstract bit<16> f(in bit<16> ix);
    abstract void g(inout data ix);
}
control c(inout bit<16> p) {
    bit<16> tmp_0;
    @name("cntr") Virtual() cntr = {
        bit<16> f(in bit<16> ix) {
            return ix + 16w1;
        }
        void g(inout data x) {
            data ix_1;
            ix_1 = x;
            if (ix_1.a < ix_1.b) {
                x.a = ix_1.a + 16w1;
            }
            if (ix_1.a > ix_1.b) {
                x.a = ix_1.a + 16w65535;
            }
        }
    };
    apply {
        tmp_0 = cntr.f(16w6);
        p = tmp_0;
    }
}
control ctr(inout bit<16> x);
package top(ctr ctrl);
top(c()) main;
