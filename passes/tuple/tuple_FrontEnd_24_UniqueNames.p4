struct S {
    bit<32> f;
    bool    s;
}
control proto();
package top(proto _p);
control c() {
    tuple<bit<32>, bool> x_0 = { 32w10, false };
    tuple<bit<32>, bool> y_0;
    apply {
        y_0 = x_0;
    }
}
top(c()) main;
