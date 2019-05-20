*** dumps/p4_16_samples/issue512.p4/pruned/issue512-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:59:17.383734400 +0200
--- dumps/p4_16_samples/issue512.p4/pruned/issue512-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:59:17.407819000 +0200
*************** parser parserI(packet_in pkt, out Parsed
*** 25,32 ****
      }
  }
  control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
      @name("cIngress.foo") action foo_0() {
!         bool hasReturned_0 = false;
          meta.b = meta.b + 4w5;
          if (meta.b > 4w10) {
              meta.b = meta.b ^ 4w5;
--- 25,33 ----
      }
  }
  control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
+     bool hasReturned_0;
      @name("cIngress.foo") action foo_0() {
!         hasReturned_0 = false;
          meta.b = meta.b + 4w5;
          if (meta.b > 4w10) {
              meta.b = meta.b ^ 4w5;
