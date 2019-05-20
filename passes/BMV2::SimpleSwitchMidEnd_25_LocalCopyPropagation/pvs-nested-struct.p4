*** dumps/p4_16_samples/pvs-nested-struct.p4/pruned/pvs-nested-struct-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:00:43.578839400 +0200
--- dumps/p4_16_samples/pvs-nested-struct.p4/pruned/pvs-nested-struct-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:00:43.582356800 +0200
*************** control MyVerifyChecksum(inout my_packet
*** 35,41 ****
      }
  }
  control MyIngress(inout my_packet p, inout my_metadata meta, inout standard_metadata_t s) {
-     bit<32> key_0;
      @name(".NoAction") action NoAction_0() {
      }
      @name("MyIngress.set_data") action set_data_0() {
--- 35,40 ----
*************** control MyIngress(inout my_packet p, ino
*** 46,58 ****
              @defaultonly NoAction_0();
          }
          key = {
!             key_0: exact @name("meta.data[0].da") ;
          }
          default_action = NoAction_0();
      }
      apply {
          {
-             key_0 = meta.data[0].da;
              t.apply();
          }
      }
--- 45,56 ----
              @defaultonly NoAction_0();
          }
          key = {
!             meta.data[0].da: exact @name("meta.data[0].da") ;
          }
          default_action = NoAction_0();
      }
      apply {
          {
              t.apply();
          }
      }
