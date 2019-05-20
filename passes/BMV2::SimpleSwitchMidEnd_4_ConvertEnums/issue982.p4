*** dumps/p4_16_samples/issue982.p4/pruned/issue982-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:59:39.709204600 +0200
--- dumps/p4_16_samples/issue982.p4/pruned/issue982-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-05-20 16:59:39.713162100 +0200
*************** typedef bit<14> PacketLength_t;
*** 21,39 ****
  typedef bit<16> EgressInstance_t;
  typedef bit<48> Timestamp_t;
  typedef error ParserError_t;
- enum InstanceType_t {
-     NORMAL,
-     CLONE,
-     RESUBMIT,
-     RECIRCULATE
- }
  struct psa_ingress_parser_input_metadata_t {
!     PortId_t       ingress_port;
!     InstanceType_t instance_type;
  }
  struct psa_egress_parser_input_metadata_t {
      PortId_t        egress_port;
!     InstanceType_t  instance_type;
      CloneMetadata_t clone_metadata;
  }
  struct psa_parser_output_metadata_t {
--- 21,33 ----
  typedef bit<16> EgressInstance_t;
  typedef bit<48> Timestamp_t;
  typedef error ParserError_t;
  struct psa_ingress_parser_input_metadata_t {
!     PortId_t ingress_port;
!     bit<32>  instance_type;
  }
  struct psa_egress_parser_input_metadata_t {
      PortId_t        egress_port;
!     bit<32>         instance_type;
      CloneMetadata_t clone_metadata;
  }
  struct psa_parser_output_metadata_t {
*************** struct psa_egress_deparser_output_metada
*** 46,55 ****
      CloneMetadata_t clone_metadata;
  }
  struct psa_ingress_input_metadata_t {
!     PortId_t       ingress_port;
!     InstanceType_t instance_type;
!     Timestamp_t    ingress_timestamp;
!     ParserError_t  parser_error;
  }
  struct psa_ingress_output_metadata_t {
      ClassOfService_t class_of_service;
--- 40,49 ----
      CloneMetadata_t clone_metadata;
  }
  struct psa_ingress_input_metadata_t {
!     PortId_t      ingress_port;
!     bit<32>       instance_type;
!     Timestamp_t   ingress_timestamp;
!     ParserError_t parser_error;
  }
  struct psa_ingress_output_metadata_t {
      ClassOfService_t class_of_service;
*************** struct psa_ingress_output_metadata_t {
*** 66,72 ****
  struct psa_egress_input_metadata_t {
      ClassOfService_t class_of_service;
      PortId_t         egress_port;
!     InstanceType_t   instance_type;
      EgressInstance_t instance;
      Timestamp_t      egress_timestamp;
      ParserError_t    parser_error;
--- 60,66 ----
  struct psa_egress_input_metadata_t {
      ClassOfService_t class_of_service;
      PortId_t         egress_port;
!     bit<32>          instance_type;
      EgressInstance_t instance;
      Timestamp_t      egress_timestamp;
      ParserError_t    parser_error;
*************** extern resubmit {
*** 96,117 ****
  extern recirculate {
      void emit<T>(in T hdr);
  }
- enum HashAlgorithm_t {
-     IDENTITY,
-     CRC32,
-     CRC32_CUSTOM,
-     CRC16,
-     CRC16_CUSTOM,
-     ONES_COMPLEMENT16,
-     TARGET_DEFAULT
- }
  extern Hash<O> {
!     Hash(HashAlgorithm_t algo);
      O get_hash<D>(in D data);
      O get_hash<T, D>(in T base, in D data, in T max);
  }
  extern Checksum<W> {
!     Checksum(HashAlgorithm_t hash);
      void clear();
      void update<T>(in T data);
      W get();
--- 90,102 ----
  extern recirculate {
      void emit<T>(in T hdr);
  }
  extern Hash<O> {
!     Hash(bit<32> algo);
      O get_hash<D>(in D data);
      O get_hash<T, D>(in T base, in D data, in T max);
  }
  extern Checksum<W> {
!     Checksum(bit<32> hash);
      void clear();
      void update<T>(in T data);
      W get();
*************** extern InternetChecksum {
*** 123,159 ****
      void remove<T>(in T data);
      bit<16> get();
  }
- enum CounterType_t {
-     PACKETS,
-     BYTES,
-     PACKETS_AND_BYTES
- }
  extern Counter<W, S> {
!     Counter(bit<32> n_counters, CounterType_t type);
      void count(in S index);
  }
  extern DirectCounter<W> {
!     DirectCounter(CounterType_t type);
      void count();
  }
- enum MeterType_t {
-     PACKETS,
-     BYTES
- }
- enum MeterColor_t {
-     RED,
-     GREEN,
-     YELLOW
- }
  extern Meter<S> {
!     Meter(bit<32> n_meters, MeterType_t type);
!     MeterColor_t execute(in S index, in MeterColor_t color);
!     MeterColor_t execute(in S index);
  }
  extern DirectMeter {
!     DirectMeter(MeterType_t type);
!     MeterColor_t execute(in MeterColor_t color);
!     MeterColor_t execute();
  }
  extern Register<T, S> {
      Register(bit<32> size);
--- 108,130 ----
      void remove<T>(in T data);
      bit<16> get();
  }
  extern Counter<W, S> {
!     Counter(bit<32> n_counters, bit<32> type);
      void count(in S index);
  }
  extern DirectCounter<W> {
!     DirectCounter(bit<32> type);
      void count();
  }
  extern Meter<S> {
!     Meter(bit<32> n_meters, bit<32> type);
!     bit<32> execute(in S index, in bit<32> color);
!     bit<32> execute(in S index);
  }
  extern DirectMeter {
!     DirectMeter(bit<32> type);
!     bit<32> execute(in bit<32> color);
!     bit<32> execute();
  }
  extern Register<T, S> {
      Register(bit<32> size);
*************** extern ActionProfile {
*** 168,174 ****
      ActionProfile(bit<32> size);
  }
  extern ActionSelector {
!     ActionSelector(HashAlgorithm_t algo, bit<32> size, bit<32> outputWidth);
  }
  extern Digest<T> {
      Digest(PortId_t receiver);
--- 139,145 ----
      ActionProfile(bit<32> size);
  }
  extern ActionSelector {
!     ActionSelector(bit<32> algo, bit<32> size, bit<32> outputWidth);
  }
  extern Digest<T> {
      Digest(PortId_t receiver);
*************** parser EgressParserImpl(packet_in buffer
*** 225,232 ****
      metadata user_meta_4;
      state start {
          transition select(istd.instance_type) {
!             InstanceType_t.CLONE: parse_clone_header;
!             InstanceType_t.NORMAL: parse_ethernet;
          }
      }
      state parse_ethernet {
--- 196,203 ----
      metadata user_meta_4;
      state start {
          transition select(istd.instance_type) {
!             32w1: parse_clone_header;
!             32w0: parse_ethernet;
          }
      }
      state parse_ethernet {
