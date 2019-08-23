#include <core.p4>
header h {
}
control c(out bit<32> x) {
    apply {
        bit<32> sz_0 = 32w4;
        x = sz_0;
    }
}
control Simpler(out bit<32> x);
package top(Simpler ctr);
top(c()) main;
