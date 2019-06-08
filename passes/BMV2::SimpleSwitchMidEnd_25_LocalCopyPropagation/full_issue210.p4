#include <core.p4>
control Ing(out bit<32> a) {
    bool b;
    @name("Ing.cond") action cond_0() {
        {
            {
                a = (b ? 32w5 : a);
                a = (!b ? 32w10 : a);
            }
        }
    }
    apply {
        b = true;
        cond_0();
    }
}
control s(out bit<32> a);
package top(s e);
top(Ing()) main;
