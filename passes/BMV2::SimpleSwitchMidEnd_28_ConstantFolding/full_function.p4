control c(out bit<16> b) {
    bool hasReturned;
    bit<16> retval;
    apply {
        {
            hasReturned = false;
            ;
            if (!hasReturned) {
                hasReturned = true;
                retval = 16w12;
            }
        }
        b = retval;
    }
}
control ctr(out bit<16> b);
package top(ctr _c);
top(c()) main;
