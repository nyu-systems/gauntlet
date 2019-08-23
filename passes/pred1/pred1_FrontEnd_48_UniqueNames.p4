#include <core.p4>
#include <v1model.p4>
control empty();
package top(empty e);
control Ing() {
    bool b;
    bit<32> a;
    @name("cond") action cond() {
        b = true;
    }
    apply {
        a = 32w2;
        cond();
    }
}
top(Ing()) main;
