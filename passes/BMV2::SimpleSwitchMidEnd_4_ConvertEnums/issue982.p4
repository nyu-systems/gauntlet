--- before_pass
+++ after_pass
@@ -21,19 +21,13 @@ typedef bit<14> PacketLength_t;
 typedef bit<16> EgressInstance_t;
 typedef bit<48> Timestamp_t;
 typedef error ParserError_t;
-enum InstanceType_t {
-    NORMAL,
-    CLONE,
-    RESUBMIT,
-    RECIRCULATE
-}
 struct psa_ingress_parser_input_metadata_t {
-    PortId_t       ingress_port;
-    InstanceType_t instance_type;
+    PortId_t ingress_port;
+    bit<32>  instance_type;
 }
 struct psa_egress_parser_input_metadata_t {
     PortId_t        egress_port;
-    InstanceType_t  instance_type;
+    bit<32>         instance_type;
     CloneMetadata_t clone_metadata;
 }
 struct psa_parser_output_metadata_t {
@@ -46,10 +40,10 @@ struct psa_egress_deparser_output_metada
     CloneMetadata_t clone_metadata;
 }
 struct psa_ingress_input_metadata_t {
-    PortId_t       ingress_port;
-    InstanceType_t instance_type;
-    Timestamp_t    ingress_timestamp;
-    ParserError_t  parser_error;
+    PortId_t      ingress_port;
+    bit<32>       instance_type;
+    Timestamp_t   ingress_timestamp;
+    ParserError_t parser_error;
 }
 struct psa_ingress_output_metadata_t {
     ClassOfService_t class_of_service;
@@ -66,7 +60,7 @@ struct psa_ingress_output_metadata_t {
 struct psa_egress_input_metadata_t {
     ClassOfService_t class_of_service;
     PortId_t         egress_port;
-    InstanceType_t   instance_type;
+    bit<32>          instance_type;
     EgressInstance_t instance;
     Timestamp_t      egress_timestamp;
     ParserError_t    parser_error;
@@ -96,22 +90,13 @@ extern resubmit {
 extern recirculate {
     void emit<T>(in T hdr);
 }
-enum HashAlgorithm_t {
-    IDENTITY,
-    CRC32,
-    CRC32_CUSTOM,
-    CRC16,
-    CRC16_CUSTOM,
-    ONES_COMPLEMENT16,
-    TARGET_DEFAULT
-}
 extern Hash<O> {
-    Hash(HashAlgorithm_t algo);
+    Hash(bit<32> algo);
     O get_hash<D>(in D data);
     O get_hash<T, D>(in T base, in D data, in T max);
 }
 extern Checksum<W> {
-    Checksum(HashAlgorithm_t hash);
+    Checksum(bit<32> hash);
     void clear();
     void update<T>(in T data);
     W get();
@@ -123,37 +108,23 @@ extern InternetChecksum {
     void remove<T>(in T data);
     bit<16> get();
 }
-enum CounterType_t {
-    PACKETS,
-    BYTES,
-    PACKETS_AND_BYTES
-}
 extern Counter<W, S> {
-    Counter(bit<32> n_counters, CounterType_t type);
+    Counter(bit<32> n_counters, bit<32> type);
     void count(in S index);
 }
 extern DirectCounter<W> {
-    DirectCounter(CounterType_t type);
+    DirectCounter(bit<32> type);
     void count();
 }
-enum MeterType_t {
-    PACKETS,
-    BYTES
-}
-enum MeterColor_t {
-    RED,
-    GREEN,
-    YELLOW
-}
 extern Meter<S> {
-    Meter(bit<32> n_meters, MeterType_t type);
-    MeterColor_t execute(in S index, in MeterColor_t color);
-    MeterColor_t execute(in S index);
+    Meter(bit<32> n_meters, bit<32> type);
+    bit<32> execute(in S index, in bit<32> color);
+    bit<32> execute(in S index);
 }
 extern DirectMeter {
-    DirectMeter(MeterType_t type);
-    MeterColor_t execute(in MeterColor_t color);
-    MeterColor_t execute();
+    DirectMeter(bit<32> type);
+    bit<32> execute(in bit<32> color);
+    bit<32> execute();
 }
 extern Register<T, S> {
     Register(bit<32> size);
@@ -168,7 +139,7 @@ extern ActionProfile {
     ActionProfile(bit<32> size);
 }
 extern ActionSelector {
-    ActionSelector(HashAlgorithm_t algo, bit<32> size, bit<32> outputWidth);
+    ActionSelector(bit<32> algo, bit<32> size, bit<32> outputWidth);
 }
 extern Digest<T> {
     Digest(PortId_t receiver);
@@ -225,8 +196,8 @@ parser EgressParserImpl(packet_in buffer
     metadata user_meta_4;
     state start {
         transition select(istd.instance_type) {
-            InstanceType_t.CLONE: parse_clone_header;
-            InstanceType_t.NORMAL: parse_ethernet;
+            32w1: parse_clone_header;
+            32w0: parse_ethernet;
         }
     }
     state parse_ethernet {
