#include <core.p4>
#include <v1model.p4>
control C(bit<1> meta) {
    apply {
        if (meta & 1w0x0 == 1w0) {
            digest(32w0, meta);
        }
    }
}
