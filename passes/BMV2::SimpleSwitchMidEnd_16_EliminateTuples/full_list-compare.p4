struct S {
    bit<32> l;
    bit<32> r;
}
control c(out bool z);
package top(c _c);
struct tuple_0 {
    bit<32> field;
    bit<32> field_0;
}
control test(out bool zout) {
    tuple_0 p;
    S q;
    apply {
        p = { 32w4, 32w5 };
        q = { 32w2, 32w3 };
        zout = p == { 32w4, 32w5 };
        zout = zout && q == { 32w2, 32w3 };
    }
}
top(test()) main;
