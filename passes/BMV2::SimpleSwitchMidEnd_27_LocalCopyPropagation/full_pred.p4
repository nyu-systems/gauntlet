#include <core.p4>
#include <v1model.p4>
control empty();
package top(empty e);
control Ing() {
    @name("Ing.cond") action cond() {
    }
    apply {
        cond();
    }
}
top(Ing()) main;
