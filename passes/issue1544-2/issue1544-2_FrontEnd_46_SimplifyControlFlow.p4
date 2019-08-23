control c(inout bit<32> x) {
    bit<32> tmp_0;
    bit<32> tmp_1;
    bit<32> tmp_2;
    bit<32> tmp_3;
    bit<32> tmp_4;
    apply {
        {
            bit<32> a_0 = x;
            bit<32> b_0 = x + 32w1;
            bool hasReturned = false;
            bit<32> retval;
            bit<32> tmp;
            if (a_0 > b_0) {
                tmp = b_0;
            } else {
                tmp = a_0;
            }
            hasReturned = true;
            retval = tmp;
            tmp_0 = retval;
        }
        tmp_1 = tmp_0;
        {
            bit<32> a_1 = x;
            bit<32> b_1 = x + 32w4294967295;
            bool hasReturned = false;
            bit<32> retval;
            bit<32> tmp;
            if (a_1 > b_1) {
                tmp = b_1;
            } else {
                tmp = a_1;
            }
            hasReturned = true;
            retval = tmp;
            tmp_2 = retval;
        }
        tmp_3 = tmp_2;
        {
            bit<32> a_2 = tmp_1;
            bit<32> b_2 = tmp_3;
            bool hasReturned = false;
            bit<32> retval;
            bit<32> tmp;
            if (a_2 > b_2) {
                tmp = b_2;
            } else {
                tmp = a_2;
            }
            hasReturned = true;
            retval = tmp;
            tmp_4 = retval;
        }
        x = tmp_4;
    }
}
control ctr(inout bit<32> x);
package top(ctr _c);
top(c()) main;
