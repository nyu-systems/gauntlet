control c(out bit<16> b) {
    bool hasReturned_0;
    bit<16> retval_0;
    apply {
        {
            hasReturned_0 = false;
            if (16w10 > 16w12) {
                hasReturned_0 = true;
                retval_0 = 16w10;
            }
            if (!hasReturned_0) {
                hasReturned_0 = true;
                retval_0 = 16w12;
            }
        }
        b = retval_0;
    }
}
control ctr(out bit<16> b);
package top(ctr _c);
top(c()) main;
