#include <core.p4>
struct intrinsic_metadata_t {
    bit<8> f0;
    bit<8> f1;
}
struct empty_t {
}
control C<H, M>(inout H hdr, inout M meta, in intrinsic_metadata_t intr_md);
package P<H, M>(C<H, M> c);
struct hdr_t {
}
struct meta_t {
    bit<8> f0;
    bit<8> f1;
    bit<8> f2;
}
control MyC(inout hdr_t hdr, inout meta_t meta, in intrinsic_metadata_t intr_md) {
    @name(".NoAction") action NoAction_0() {
    }
    bit<8> key_0;
    @name("MyC.c2.a") table c2_a {
        key = {
            key_0: exact @name("meta.f0") ;
        }
        actions = {
            NoAction_0();
        }
        default_action = NoAction_0();
    }
    apply {
        {
            key_0 = meta_t {f0 = 8w0,f1 = 8w0,f2 = 8w0}.f0;
            c2_a.apply();
        }
    }
}
P<hdr_t, meta_t>(MyC()) main;
