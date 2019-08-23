extern void f(in bit<16> x, in bool y);
control c() {
    apply {
        f(x = 16w0, y = true);
    }
}
control empty();
package top(empty _e);
top(c()) main;
