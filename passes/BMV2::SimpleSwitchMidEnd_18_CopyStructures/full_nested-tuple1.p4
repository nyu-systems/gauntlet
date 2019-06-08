struct T {
    bit<1> f;
}
struct tuple_0 {
    T field;
    T field_0;
}
struct S {
    tuple_0 f1;
    T       f2;
    bit<1>  z;
}
extern void f<D>(in D data);
control c(inout bit<1> r) {
    S s_0;
    bit<1> tmp;
    apply {
        {
            {
                {
                    s_0.f1.field.f = 1w0;
                }
                {
                    s_0.f1.field_0.f = 1w1;
                }
            }
            {
                s_0.f2.f = 1w0;
            }
            s_0.z = 1w1;
        }
        f<tuple_0>(s_0.f1);
        tmp = s_0.f2.f & s_0.z;
        r = tmp;
    }
}
control simple(inout bit<1> r);
package top(simple e);
top(c()) main;
