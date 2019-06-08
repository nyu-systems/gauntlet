extern bit<32> f(in bit<32> x);
control c(inout bit<32> r) {
    bit<32> tmp_3;
    bit<32> tmp_5;
    apply {
        tmp_5 = f(32w2);
        if (tmp_5 > 32w0) {
            tmp_3 = f(32w2);
            if (tmp_3 < 32w2) 
                r = 32w1;
            else 
                r = 32w3;
        }
        else 
            r = 32w2;
    }
}
control simple(inout bit<32> r);
package top(simple e);
top(c()) main;
