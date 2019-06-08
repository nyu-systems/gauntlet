extern bit<32> f(in bit<32> x);
control c(inout bit<32> r) {
    bit<32> tmp_7;
    bool tmp_9;
    bit<32> tmp_10;
    bool tmp_12;
    bit<32> tmp_13;
    apply {
        tmp_7 = f(32w2);
        if (!(tmp_7 > 32w0)) 
            tmp_9 = false;
        else {
            tmp_10 = f(32w3);
            tmp_9 = tmp_10 < 32w0;
        }
        if (tmp_9) 
            tmp_12 = true;
        else {
            tmp_13 = f(32w5);
            tmp_12 = tmp_13 == 32w2;
        }
        if (tmp_12) 
            r = 32w1;
        else 
            r = 32w2;
    }
}
control simple(inout bit<32> r);
package top(simple e);
top(c()) main;
