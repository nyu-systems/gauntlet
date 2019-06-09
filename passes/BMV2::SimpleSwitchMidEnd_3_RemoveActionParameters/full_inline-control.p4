extern Y {
    Y(bit<32> b);
    bit<32> get();
}
control d(out bit<32> x) {
    bit<32> cinst_tmp;
    @name("d.cinst.y") Y(32w16) cinst_y;
    apply {
        cinst_tmp = cinst_y.get();
        x = cinst_tmp;
    }
}
control dproto(out bit<32> x);
package top(dproto _d);
top(d()) main;
