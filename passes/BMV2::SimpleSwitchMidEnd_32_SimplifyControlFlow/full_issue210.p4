#include <core.p4>
control Ing(out bit<32> a) {
    bool b_0;
    @name("Ing.cond") action cond() {
        a = (b_0 ? 32w5 : a);
        a = (!b_0 ? 32w10 : a);
    }
    apply {
        b_0 = true;
        cond();
    }
}
control s(out bit<32> a);
package top(s e);
top(Ing()) main;
