control proto(out bit<32> x);
package top(proto _c);
control c(out bit<32> x) {
    apply {
        x = 8w0xf ++ 16w0xf ++ 8w0xf + (16w0xf ++ (8w0xf ++ 8w0xf));
    }
}
top(c()) main;
