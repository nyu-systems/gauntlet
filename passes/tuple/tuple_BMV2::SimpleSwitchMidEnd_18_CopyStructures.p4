struct S {
    bit<32> f;
    bool    s;
}
control proto();
package top(proto _p);
struct tuple_0 {
    bit<32> field;
    bool    field_0;
}
control c() {
    tuple_0 x_0;
    apply {
        {
            x_0.field = 32w10;
            x_0.field_0 = false;
        }
    }
}
top(c()) main;
