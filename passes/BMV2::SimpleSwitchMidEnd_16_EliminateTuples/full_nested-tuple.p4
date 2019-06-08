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
    S s;
    apply {
        s = { { { 1w0 }, { 1w1 } }, { 1w0 }, 1w1 };
        f<tuple_1>(s.f1);
        f<tuple_0>({ { 1w0 }, { 1w1 } });
        r = s.f2.f & s.z;
    }
}
control simple(inout bit<1> r);
package top(simple e);
top(c()) main;
