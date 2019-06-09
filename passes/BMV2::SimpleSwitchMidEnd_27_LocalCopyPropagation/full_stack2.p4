#include <core.p4>
header h {
}
control c(out bit<32> x) {
    apply {
        x = 32w4;
    }
}
control Simpler(out bit<32> x);
package top(Simpler ctr);
top(c()) main;
