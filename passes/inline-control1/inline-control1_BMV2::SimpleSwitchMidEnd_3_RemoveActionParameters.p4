extern Y {
    Y(bit<32> b);
    bit<32> get();
}
control d(out bit<32> x) {
    bit<32> y_0;
    bit<32> x_0;
    bit<32> cinst_tmp;
    @name("d.cinst.y") Y(32w16) cinst_y;
    apply {
        cinst_tmp = cinst_y.get();
        x_0 = cinst_tmp;
        x = x_0;
        cinst_tmp = cinst_y.get();
        x_0 = cinst_tmp;
        y_0 = x_0;
    }
}
control dproto(out bit<32> x);
package top(dproto _d);
top(d()) main;
