bit<32> min(in bit<32> a, in bit<32> b) {
    bool hasReturned = false;
    bit<32> retval;
    bit<32> tmp;
    if (a > b) {
        tmp = b;
    } else {
        tmp = a;
    }
    {
        hasReturned = true;
        retval = tmp;
    }
    return retval;
}
control c(inout bit<32> x) {
    bit<32> tmp_0;
    bit<32> tmp_1;
    bit<32> tmp_2;
    bit<32> tmp_3;
    bit<32> tmp_4;
    apply {
        tmp_0 = min(x, x + 32w1);
        tmp_1 = tmp_0;
        tmp_2 = min(x, x + 32w4294967295);
        tmp_3 = tmp_2;
        tmp_4 = min(tmp_1, tmp_3);
        x = tmp_4;
    }
}
control ctr(inout bit<32> x);
package top(ctr _c);
top(c()) main;
