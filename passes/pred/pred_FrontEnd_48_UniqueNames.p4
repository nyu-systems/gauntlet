#include <core.p4>
#include <v1model.p4>
control empty();
package top(empty e);
control Ing() {
    bool b;
    @name("cond") action cond() {
        b = true;
    }
    apply {
        cond();
    }
}
top(Ing()) main;
