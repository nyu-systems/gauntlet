#include <core.p4>
control Ing(out bit<32> a) {
    bool b;
    action cond() {
        if (b) {
            a = (bit<32>)32w5;
        } else {
            a = (bit<32>)32w10;
        }
    }
    apply {
        b = true;
        cond();
    }
}
control s(out bit<32> a);
package top(s e);
top(Ing()) main;
