control c(inout bit<32> x) {
    apply {
        x = 32w10;
        if (32w10 == 32w10) {
            x = 32w10 + 32w2;
            x = 32w10 + 32w2 + 32w4294967290;
        } else {
            x = 32w10 << 2;
        }
    }
}
control n(inout bit<32> x);
package top(n _n);
top(c()) main;
