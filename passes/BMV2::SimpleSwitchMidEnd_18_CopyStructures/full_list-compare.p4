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
        {
            p.field = 32w4;
            p.field_0 = 32w5;
        }
        {
            q.l = 32w2;
            q.r = 32w3;
        }
        zout = true && p.field == 32w4 && p.field_0 == 32w5;
        zout = zout && (true && q.l == 32w2 && q.r == 32w3);
    }
}
top(test()) main;
