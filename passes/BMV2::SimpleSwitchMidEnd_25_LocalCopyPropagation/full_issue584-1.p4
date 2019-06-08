#include <core.p4>
#include <v1model.p4>
control p();
package top(p _p);
control c() {
    bit<16> var;
    apply {
        hash<bit<16>, bit<16>, bit<32>, bit<16>>(var, HashAlgorithm.crc16, 16w0, 32w0, 16w0xffff);
    }
}
top(c()) main;
