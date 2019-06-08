extern void f(in bit<16> x, in bool y);
control c() {
    bit<16> xv;
    bool b;
    apply {
        xv = 16w0;
        b = true;
        f(x = xv, y = b);
    }
}
control empty();
package top(empty _e);
top(c()) main;
