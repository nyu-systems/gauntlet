extern Y {
    Y(bit<32> b);
    bit<32> get();
}
control d(out bit<32> x) {
    bit<32> cinst_tmp_0;
    @name("d.cinst.y") Y(32w16) cinst_y_0;
    apply {
        cinst_tmp_0 = cinst_y_0.get();
        x = cinst_tmp_0;
        cinst_tmp_0 = cinst_y_0.get();
    }
}
control dproto(out bit<32> x);
package top(dproto _d);
top(d()) main;
