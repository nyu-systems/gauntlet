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
    tuple_0 p_0;
    S q_0;
    apply {
        p_0 = { 32w4, 32w5 };
        q_0 = { 32w2, 32w3 };
        zout = p_0 == { 32w4, 32w5 };
        zout = zout && q_0 == S {l = 32w2,r = 32w3};
    }
}
top(test()) main;
