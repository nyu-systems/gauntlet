extern bit<1> f(inout bit<1> x, in bit<1> y);
extern bit<1> g(inout bit<1> x);
header H {
    bit<1> z;
}
control c();
package top(c _c);
control my() {
    bit<1> a_0;
    H[2] s_0;
    apply {
        a_0 = 1w0;
        a_0 = f(a_0, g(a_0));
        a_0 = f(s_0[a_0].z, g(a_0));
        a_0 = f(s_0[g(a_0)].z, a_0);
        a_0 = g(a_0);
        a_0[0:0] = g(a_0[0:0]);
        s_0[a_0].z = g(a_0);
    }
}
top(my()) main;
