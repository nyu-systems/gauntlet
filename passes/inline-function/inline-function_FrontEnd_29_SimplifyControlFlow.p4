bit<32> min(in bit<32> a, in bit<32> b) {
    bit<32> tmp;
    if (a > b) {
        tmp = b;
    } else {
        tmp = a;
    }
    return tmp;
}
bit<32> fun(in bit<32> a, in bit<32> b) {
    bit<32> tmp_0;
    bit<32> tmp_1;
    tmp_0 = min(a, b);
    tmp_1 = a + tmp_0;
    return tmp_1;
}
control c(inout bit<32> x) {
    bit<32> tmp_2;
    apply {
        tmp_2 = fun(x, x);
        x = tmp_2;
    }
}
control ctr(inout bit<32> x);
package top(ctr _c);
top(c()) main;
