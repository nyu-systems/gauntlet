*** dumps/p4_16_samples/issue949.p4/pruned/issue949-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:38.011352400 +0200
--- dumps/p4_16_samples/issue949.p4/pruned/issue949-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:38.014753700 +0200
*************** control egress(inout headers hdr, inout
*** 38,44 ****
      }
  }
  control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
-     bool tmp_0;
      @name(".NoAction") action NoAction_0() {
      }
      @name("ingress.setDest") action setDest_0() {
--- 38,43 ----
*************** control ingress(inout headers hdr, inout
*** 55,61 ****
          default_action = NoAction_0();
      }
      apply {
!         tmp_0 = someTable.apply().hit;
      }
  }
  control DeparserImpl(packet_out packet, in headers hdr) {
--- 54,60 ----
          default_action = NoAction_0();
      }
      apply {
!         someTable.apply();
      }
  }
  control DeparserImpl(packet_out packet, in headers hdr) {
