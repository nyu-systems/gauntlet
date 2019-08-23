struct T {
    bit<1> f;
}
struct tuple_1 {
    T field_1;
    T field_2;
}
struct S {
    tuple_1 f1;
    T       f2;
    bit<1>  z;
}
struct tuple_0 {
    T field;
    T field_0;
}
extern void f<T>(in T data);
control c(inout bit<1> r) {
    T s_0_f1_field;
    T s_0_f1_field_0;
    T s_0_f2;
    bit<1> s_0_z;
    apply {
        {
            {
                {
                    s_0_f1_field.f = 1w0;
                }
                {
                    s_0_f1_field_0.f = 1w1;
                }
            }
            {
                s_0_f2.f = 1w0;
            }
            s_0_z = 1w1;
        }
        f<tuple_1>({ s_0_f1_field, s_0_f1_field_0 });
        f<tuple_0>(tuple_0 {field = T {f = 1w0},field_0 = T {f = 1w1}});
        r = s_0_f2.f & s_0_z;
    }
}
control simple(inout bit<1> r);
package top(simple e);
top(c()) main;
