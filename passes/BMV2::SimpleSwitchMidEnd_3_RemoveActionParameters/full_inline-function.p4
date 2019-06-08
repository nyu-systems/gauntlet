control c(inout bit<32> x) {
    bit<32> tmp_3;
    bit<32> a;
    bit<32> b;
    bool hasReturned_1;
    bit<32> retval_1;
    bit<32> tmp_4;
    bit<32> tmp_5;
    bit<32> a_2;
    bit<32> b_2;
    bool hasReturned_2;
    bit<32> retval_2;
    bit<32> tmp_6;
    apply {
        {
            a = x;
            b = x;
            hasReturned_1 = false;
            {
                a_2 = a;
                b_2 = b;
                hasReturned_2 = false;
                if (a_2 > b_2) 
                    tmp_6 = b_2;
                else 
                    tmp_6 = a_2;
                hasReturned_2 = true;
                retval_2 = tmp_6;
                tmp_4 = retval_2;
            }
            tmp_5 = a + tmp_4;
            hasReturned_1 = true;
            retval_1 = tmp_5;
            tmp_3 = retval_1;
        }
        x = tmp_3;
    }
}
control ctr(inout bit<32> x);
package top(ctr _c);
top(c()) main;
