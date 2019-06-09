control c(inout bit<32> x) {
    bit<32> tmp_4;
    bit<32> tmp_11;
    bit<32> tmp_12;
    apply {
        if (x > x + 32w1) 
            tmp_4 = x + 32w1;
        else 
            tmp_4 = x;
        if (x > x + 32w4294967295) 
            tmp_11 = x + 32w4294967295;
        else 
            tmp_11 = x;
        if (tmp_4 > tmp_11) 
            tmp_12 = tmp_11;
        else 
            tmp_12 = tmp_4;
        x = tmp_12;
    }
}
control ctr(inout bit<32> x);
package top(ctr _c);
top(c()) main;
