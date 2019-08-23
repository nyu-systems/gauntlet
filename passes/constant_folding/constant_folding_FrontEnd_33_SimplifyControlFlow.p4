control proto(out bit<32> x);
package top(proto _c);
control c(out bit<32> x) {
    bool w_0;
    bit<8> z_0;
    apply {
        x = 32w17;
    }
}
top(c()) main;
