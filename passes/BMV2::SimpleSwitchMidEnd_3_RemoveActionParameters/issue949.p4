*** dumps/p4_16_samples/issue949.p4/pruned/issue949-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:59:38.029107000 +0200
--- dumps/p4_16_samples/issue949.p4/pruned/issue949-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:59:38.054168100 +0200
*************** control egress(inout headers hdr, inout
*** 38,46 ****
      }
  }
  control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
      @name(".NoAction") action NoAction_0() {
      }
-     bool tmp_0;
      @name("ingress.setDest") action setDest_0() {
          hdr.ethernet.dstAddr = 48w0x6af3400426d3;
      }
--- 38,46 ----
      }
  }
  control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
+     bool tmp_0;
      @name(".NoAction") action NoAction_0() {
      }
      @name("ingress.setDest") action setDest_0() {
          hdr.ethernet.dstAddr = 48w0x6af3400426d3;
      }
