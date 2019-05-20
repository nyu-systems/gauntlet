*** dumps/p4_16_samples/pvs-nested-struct.p4/pruned/pvs-nested-struct-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:00:43.600048000 +0200
--- dumps/p4_16_samples/pvs-nested-struct.p4/pruned/pvs-nested-struct-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:00:43.604617400 +0200
*************** control MyIngress(inout my_packet p, ino
*** 50,58 ****
          default_action = NoAction_0();
      }
      apply {
!         {
!             t.apply();
!         }
      }
  }
  control MyEgress(inout my_packet p, inout my_metadata m, inout standard_metadata_t s) {
--- 50,56 ----
          default_action = NoAction_0();
      }
      apply {
!         t.apply();
      }
  }
  control MyEgress(inout my_packet p, inout my_metadata m, inout standard_metadata_t s) {
