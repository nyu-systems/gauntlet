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
    FieldList1_t fl1_1;
    FieldList2_t fl2_1;
    bit<16> output;
    bit<16> tmp;
    bit<16> tmp_0;
    @name("IngressI.IngressI.hash1") Hash<bit<16>>() hash1;
    apply {
        fl1_1 = FieldList1_t {a = hdr.h.fA[31:24],b = hdr.h.fB};
        fl2_1 = FieldList2_t {a = hdr.h.fB,b = hdr.h.fC,c = hdr.h.fA};
        tmp_0 = hash1.get<FieldLists_t>(FieldLists_t {fl1 = fl1_1,fl2 = fl2_1});
        tmp = tmp_0;
        output = tmp;
        smeta.egress_spec = (bit<9>)output;
    }
}
control EgressI(inout H hdr, inout M meta, inout standard_metadata_t smeta) {
    apply {
    }
}
control DeparserI(packet_out pk, in H hdr) {
    apply {
        {
            pk.emit<Hdr>(hdr.h);
        }
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
