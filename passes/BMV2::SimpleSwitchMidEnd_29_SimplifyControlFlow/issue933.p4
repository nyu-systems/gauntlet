*** dumps/p4_16_samples/issue933.p4/pruned/issue933-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:37.237564000 +0200
--- dumps/p4_16_samples/issue933.p4/pruned/issue933-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:37.293634500 +0200
*************** struct headers {
*** 5,12 ****
  }
  control MyDeparser(packet_out packet, in headers hdr) {
      apply {
-         {
-         }
      }
  }
  Switch<headers>(MyDeparser()) main;
--- 5,10 ----
