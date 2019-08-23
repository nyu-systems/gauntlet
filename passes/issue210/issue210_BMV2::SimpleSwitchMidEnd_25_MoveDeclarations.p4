#include <core.p4>
control Ing(out bit<32> a) {
    bool b_0;
    bool cond_0;
    bool pred;
    @name("Ing.cond") action cond() {
        {
            {
                cond_0 = b_0;
                pred = cond_0;
                a = (pred ? 32w5 : a);
                cond_0 = !cond_0;
                pred = cond_0;
                a = (pred ? 32w10 : a);
            }
        }
    }
    apply {
        b_0 = true;
        cond();
    }
}
control s(out bit<32> a);
package top(s e);
top(Ing()) main;
