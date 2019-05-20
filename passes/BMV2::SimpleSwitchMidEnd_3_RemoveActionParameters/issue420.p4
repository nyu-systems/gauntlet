*** dumps/p4_16_samples/issue420.p4/pruned/issue420-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:59:11.681921700 +0200
--- dumps/p4_16_samples/issue420.p4/pruned/issue420-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:59:11.708346300 +0200
*************** parser parserI(packet_in pkt, out Parsed
*** 25,34 ****
      }
  }
  control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
      @name(".NoAction") action NoAction_0() {
      }
      @name("cIngress.foo") action foo_0(bit<16> bar) {
!         bool hasReturned_1 = false;
          if (bar == 16w0xf00d) {
              hdr.ethernet.srcAddr = 48w0xdeadbeeff00d;
              hasReturned_1 = true;
--- 25,36 ----
      }
  }
  control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
+     bool hasReturned_1;
+     bool hasReturned_2;
      @name(".NoAction") action NoAction_0() {
      }
      @name("cIngress.foo") action foo_0(bit<16> bar) {
!         hasReturned_1 = false;
          if (bar == 16w0xf00d) {
              hdr.ethernet.srcAddr = 48w0xdeadbeeff00d;
              hasReturned_1 = true;
*************** control cIngress(inout Parsed_packet hdr
*** 46,52 ****
          default_action = NoAction_0();
      }
      apply {
!         bool hasReturned_2 = false;
          tbl1.apply();
          hasReturned_2 = true;
      }
--- 48,54 ----
          default_action = NoAction_0();
      }
      apply {
!         hasReturned_2 = false;
          tbl1.apply();
          hasReturned_2 = true;
      }
