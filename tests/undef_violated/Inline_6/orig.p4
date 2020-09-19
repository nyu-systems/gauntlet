error {
    NoError,
    PacketTooShort,
    NoMatch,
    StackOutOfBounds,
    HeaderTooShort,
    ParserTimeout,
    ParserInvalidArgument,
    CounterRange,
    Timeout,
    PhvOwner,
    MultiWrite,
    IbufOverflow,
    IbufUnderflow
}

extern packet_in {
    void extract<T>(out T hdr);
    void extract<T>(out T variableSizeHeader, in bit<32> variableFieldSizeInBits);
    T lookahead<T>();
    void advance(in bit<32> sizeInBits);
    bit<32> length();
}

extern packet_out {
    void emit<T>(in T hdr);
}

extern void verify(in bool check, in error toSignal);
match_kind {
    exact,
    ternary,
    lpm
}

typedef bit<10> MirrorId_t;
enum MeterType_t {
    PACKETS,
    BYTES
}

enum bit<8> MeterColor_t {
    GREEN = 8w0,
    YELLOW = 8w1,
    RED = 8w3
}

enum CounterType_t {
    PACKETS,
    BYTES,
    PACKETS_AND_BYTES
}

enum SelectorMode_t {
    FAIR,
    RESILIENT
}

enum HashAlgorithm_t {
    IDENTITY,
    RANDOM,
    CRC8,
    CRC16,
    CRC32,
    CRC64,
    CUSTOM
}

match_kind {
    range,
    selector,
    atcam_partition_index
}

@__intrinsic_metadata header ingress_intrinsic_metadata_t {
    bit<9> ingress_port;
}

@__intrinsic_metadata struct ingress_intrinsic_metadata_for_tm_t {
    bit<9> ucast_egress_port;
}

@__intrinsic_metadata struct ingress_intrinsic_metadata_from_parser_t {
    bit<16> parser_err;
}

@__intrinsic_metadata struct ingress_intrinsic_metadata_for_deparser_t {
}

@__intrinsic_metadata header egress_intrinsic_metadata_t {
}

@__intrinsic_metadata struct egress_intrinsic_metadata_from_parser_t {
}

@__intrinsic_metadata struct egress_intrinsic_metadata_for_deparser_t {
}

@__intrinsic_metadata struct egress_intrinsic_metadata_for_output_port_t {
}

extern Checksum {
    Checksum();
    void add<T>(in T data);
    void subtract<T>(in T data);
    bool verify();
    bit<16> get();
    bit<16> update<T>(in T data, @optional in bool zeros_as_ones);
}

extern ParserCounter {
    ParserCounter();
    void set<T>(in T value);
    void set<T>(in T field, in bit<8> max, in bit<8> rotate, in bit<3> mask, in bit<8> add);
    bool is_zero();
    bool is_negative();
    void increment(in bit<8> value);
    void decrement(in bit<8> value);
}

extern ParserPriority {
    ParserPriority();
    void set(in bit<3> prio);
}

extern CRCPolynomial<T> {
    CRCPolynomial(T coeff, bool reversed, bool msb, bool extended, T init, T xor);
}

extern Hash<W> {
    Hash(HashAlgorithm_t algo);
    Hash(HashAlgorithm_t algo, CRCPolynomial<_> poly);
    W get<D>(in D data);
}

extern Random<W> {
    Random();
    W get();
}

extern Counter<W, I> {
    Counter(bit<32> size, CounterType_t type);
    void count(in I index);
}

extern DirectCounter<W> {
    DirectCounter(CounterType_t type);
    void count();
}

extern Meter<I> {
    Meter(bit<32> size, MeterType_t type);
    Meter(bit<32> size, MeterType_t type, bit<8> red, bit<8> yellow, bit<8> green);
    bit<8> execute(in I index, in MeterColor_t color);
    bit<8> execute(in I index);
}

extern DirectMeter {
    DirectMeter(MeterType_t type);
    DirectMeter(MeterType_t type, bit<8> red, bit<8> yellow, bit<8> green);
    bit<8> execute(in MeterColor_t color);
    bit<8> execute();
}

extern Lpf<T, I> {
    Lpf(bit<32> size);
    T execute(in T val, in I index);
}

extern DirectLpf<T> {
    DirectLpf();
    T execute(in T val);
}

extern Wred<T, I> {
    Wred(bit<32> size, bit<8> drop_value, bit<8> no_drop_value);
    bit<8> execute(in T val, in I index);
}

extern DirectWred<T> {
    DirectWred(bit<8> drop_value, bit<8> no_drop_value);
    bit<8> execute(in T val);
}

extern Register<T, I> {
    Register(bit<32> size);
    Register(bit<32> size, T initial_value);
    T read(in I index);
    void write(in I index, in T value);
}

extern DirectRegister<T> {
    DirectRegister();
    DirectRegister(T initial_value);
    T read();
    void write(in T value);
}

extern RegisterParam<T> {
    RegisterParam(T initial_value);
    T read();
}

extern ActionProfile {
    ActionProfile(bit<32> size);
}

extern ActionSelector {
    ActionSelector(ActionProfile action_profile, Hash<_> hash, SelectorMode_t mode, bit<32> max_group_size, bit<32> num_groups);
    ActionSelector(ActionProfile action_profile, Hash<_> hash, SelectorMode_t mode, Register<bit<1>, _> reg, bit<32> max_group_size, bit<32> num_groups);
    @deprecated("ActionSelector must be specified with an associated ActionProfile") ActionSelector(bit<32> size, Hash<_> hash, SelectorMode_t mode);
    @deprecated("ActionSelector must be specified with an associated ActionProfile") ActionSelector(bit<32> size, Hash<_> hash, SelectorMode_t mode, Register<bit<1>, _> reg);
}

extern Mirror {
    Mirror();
    void emit(in MirrorId_t session_id);
    void emit<T>(in MirrorId_t session_id, in T hdr);
}

extern Resubmit {
    Resubmit();
    void emit();
    void emit<T>(in T hdr);
}

extern Digest<T> {
    Digest();
    void pack(in T data);
}

extern Atcam {
    Atcam(@optional bit<32> number_partitions);
}

extern Alpm {
    Alpm(@optional bit<32> number_partitions, @optional bit<32> subtrees_per_partition);
}

parser IngressParserT<H, M>(packet_in pkt, out H hdr, out M ig_md, @optional out ingress_intrinsic_metadata_t ig_intr_md, @optional out ingress_intrinsic_metadata_for_tm_t ig_intr_md_for_tm, @optional out ingress_intrinsic_metadata_from_parser_t ig_intr_md_from_prsr);
parser EgressParserT<H, M>(packet_in pkt, out H hdr, out M eg_md, @optional out egress_intrinsic_metadata_t eg_intr_md, @optional out egress_intrinsic_metadata_from_parser_t eg_intr_md_from_prsr);
control IngressT<H, M>(inout H hdr, inout M ig_md, @optional in ingress_intrinsic_metadata_t ig_intr_md, @optional in ingress_intrinsic_metadata_from_parser_t ig_intr_md_from_prsr, @optional inout ingress_intrinsic_metadata_for_deparser_t ig_intr_md_for_dprsr, @optional inout ingress_intrinsic_metadata_for_tm_t ig_intr_md_for_tm);
control EgressT<H, M>(inout H hdr, inout M eg_md, @optional in egress_intrinsic_metadata_t eg_intr_md, @optional in egress_intrinsic_metadata_from_parser_t eg_intr_md_from_prsr, @optional inout egress_intrinsic_metadata_for_deparser_t eg_intr_md_for_dprsr, @optional inout egress_intrinsic_metadata_for_output_port_t eg_intr_md_for_oport);
control IngressDeparserT<H, M>(packet_out pkt, inout H hdr, in M metadata, @optional in ingress_intrinsic_metadata_for_deparser_t ig_intr_md_for_dprsr, @optional in ingress_intrinsic_metadata_t ig_intr_md);
control EgressDeparserT<H, M>(packet_out pkt, inout H hdr, in M metadata, @optional in egress_intrinsic_metadata_for_deparser_t eg_intr_md_for_dprsr, @optional in egress_intrinsic_metadata_t eg_intr_md, @optional in egress_intrinsic_metadata_from_parser_t eg_intr_md_from_prsr);
package Pipeline<IH, IM, EH, EM>(IngressParserT<IH, IM> ingress_parser, IngressT<IH, IM> ingress, IngressDeparserT<IH, IM> ingress_deparser, EgressParserT<EH, EM> egress_parser, EgressT<EH, EM> egress, EgressDeparserT<EH, EM> egress_deparser);
@pkginfo(arch="TNA", version="1.0.1") package Switch<IH0, IM0, EH0, EM0, IH1, IM1, EH1, EM1, IH2, IM2, EH2, EM2, IH3, IM3, EH3, EM3>(Pipeline<IH0, IM0, EH0, EM0> pipe0, @optional Pipeline<IH1, IM1, EH1, EM1> pipe1, @optional Pipeline<IH2, IM2, EH2, EM2> pipe2, @optional Pipeline<IH3, IM3, EH3, EM3> pipe3);
header ethernet_h {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

typedef bit<16> nexthop_t;
typedef bit<128> srv6_sid_t;
struct srv6_metadata_t {
    srv6_sid_t sid;
    bit<16>    rewrite;
    bool       psp;
    bool       usp;
    bool       decap;
    bool       encap;
}

struct ingress_metadata_t {
    nexthop_t nexthop;
}

struct egress_metadata_t {
}

struct lookup_fields_t {
    bit<48> ipv4_dst_addr;
}

struct header_t {
    ethernet_h eth_hdr;
}

parser SwitchIngressParser(packet_in pkt, out header_t hdr, out ingress_metadata_t ig_md, out ingress_intrinsic_metadata_t ig_intr_md) {
    state start {
        transition accept;
    }
}

control SwitchIngressDeparser(packet_out pkt, inout header_t hdr, in ingress_metadata_t ig_md, in ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md) {
    apply {
    }
}

parser SwitchEgressParser(packet_in pkt, out header_t hdr, out egress_metadata_t eg_md, out egress_intrinsic_metadata_t eg_intr_md) {
    state start {
        transition accept;
    }
}

control SwitchEgressDeparser(packet_out pkt, inout header_t hdr, in egress_metadata_t eg_md, in egress_intrinsic_metadata_for_deparser_t eg_dprsr_md) {
    apply {
    }
}

control simple_reset(in bit<8> dst_addr, out bit<16> eth_type) {
    apply {
        if (dst_addr == 8w1) {
            eth_type = 16w1;
        }
    }
}

control SwitchIngress(inout header_t hdr, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    bit<8> undef_0;
    @name("simple_reset") simple_reset() simple_reset_inst_0;
    apply {
        if (hdr.eth_hdr.src_addr == 48w1) {
            undef_0 = 8w1;
        }
        simple_reset_inst_0.apply(undef_0, hdr.eth_hdr.eth_type);
    }
}

control SwitchEgress(inout header_t hdr, inout egress_metadata_t eg_md, in egress_intrinsic_metadata_t eg_intr_md, in egress_intrinsic_metadata_from_parser_t eg_intr_from_prsr, inout egress_intrinsic_metadata_for_deparser_t eg_intr_md_for_dprsr, inout egress_intrinsic_metadata_for_output_port_t eg_intr_md_for_oport) {
    apply {
    }
}

Pipeline<header_t, ingress_metadata_t, header_t, egress_metadata_t>(SwitchIngressParser(), SwitchIngress(), SwitchIngressDeparser(), SwitchEgressParser(), SwitchEgress(), SwitchEgressDeparser()) pipe;

Switch<header_t, ingress_metadata_t, header_t, egress_metadata_t, _, _, _, _, _, _, _, _, _, _, _, _>(pipe) main;

