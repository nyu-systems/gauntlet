*** dumps/p4_16_samples/issue983-bmv2.p4/pruned/issue983-bmv2-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:59:40.284838600 +0200
--- dumps/p4_16_samples/issue983-bmv2.p4/pruned/issue983-bmv2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:59:40.313316200 +0200
*************** parser IngressParserImpl(packet_in buffe
*** 31,41 ****
      }
  }
  control ingress(inout headers hdr, inout metadata user_meta, inout standard_metadata_t standard_metadata) {
-     @name(".NoAction") action NoAction_0() {
-     }
      bit<16> tmp_1;
      bit<32> x1_1;
      bit<16> x2_1;
      @name("ingress.debug_table_cksum1") table debug_table_cksum1 {
          key = {
              hdr.ethernet.srcAddr            : exact @name("hdr.ethernet.srcAddr") ;
--- 31,41 ----
      }
  }
  control ingress(inout headers hdr, inout metadata user_meta, inout standard_metadata_t standard_metadata) {
      bit<16> tmp_1;
      bit<32> x1_1;
      bit<16> x2_1;
+     @name(".NoAction") action NoAction_0() {
+     }
      @name("ingress.debug_table_cksum1") table debug_table_cksum1 {
          key = {
              hdr.ethernet.srcAddr            : exact @name("hdr.ethernet.srcAddr") ;
