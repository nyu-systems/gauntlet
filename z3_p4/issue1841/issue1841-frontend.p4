#include <core.p4>
#include <v1model.p4>
header Hdr {
    bit<32> fA;
    bit<16> fB;
    bit<16> fC;
    bit<16> fD;
    bit<16> fE;
    bit<32> fF;
    bit<8>  fG;
}
struct H {
    Hdr h;
}
struct M {
}
struct FieldList1_t {
    bit<8>  a;
    bit<16> b;
}
struct FieldList2_t {
    bit<16> a;
    bit<16> b;
    bit<32> c;
}
struct FieldLists_t {
    FieldList1_t fl1;
    FieldList2_t fl2;
}
extern Hash<T> {
    Hash();
    T get<I>(in I input);
}
parser ParserI(packet_in pk, out H hdr, inout M meta, inout standard_metadata_t smeta) {
    state start {
        pk.extract<Hdr>(hdr.h);
        transition accept;
    }
}
control IngressI(inout H hdr, inout M meta, inout standard_metadata_t smeta) {
    FieldList1_t fl1_0;
    FieldList2_t fl2_0;
    bit<16> output_0;
    bit<16> tmp;
    @name("IngressI.hash1") Hash<bit<16>>() hash1_0;
    apply {
        fl1_0 = { hdr.h.fA[31:24], hdr.h.fB };
        fl2_0 = { hdr.h.fB, hdr.h.fC, hdr.h.fA };
        tmp = hash1_0.get<FieldLists_t>(FieldLists_t {fl1 = fl1_0,fl2 = fl2_0});
        output_0 = tmp;
        smeta.egress_spec = (bit<9>)output_0;
    }
}
control EgressI(inout H hdr, inout M meta, inout standard_metadata_t smeta) {
    apply {
    }
}
control DeparserI(packet_out pk, in H hdr) {
    apply {
        pk.emit<H>(hdr);
    }
}
control VerifyChecksumI(inout H hdr, inout M meta) {
    apply {
    }
}
control ComputeChecksumI(inout H hdr, inout M meta) {
    apply {
    }
}
V1Switch<H, M>(ParserI(), VerifyChecksumI(), IngressI(), EgressI(), ComputeChecksumI(), DeparserI()) main;

