*** dumps/p4_16_samples/pvs-nested-struct.p4/pruned/pvs-nested-struct-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 17:00:43.567558200 +0200
--- dumps/p4_16_samples/pvs-nested-struct.p4/pruned/pvs-nested-struct-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:00:43.571926100 +0200
*************** control MyVerifyChecksum(inout my_packet
*** 35,45 ****
      }
  }
  control MyIngress(inout my_packet p, inout my_metadata meta, inout standard_metadata_t s) {
      @name(".NoAction") action NoAction_0() {
      }
      @name("MyIngress.set_data") action set_data_0() {
      }
-     bit<32> key_0;
      @name("MyIngress.t") table t {
          actions = {
              set_data_0();
--- 35,45 ----
      }
  }
  control MyIngress(inout my_packet p, inout my_metadata meta, inout standard_metadata_t s) {
+     bit<32> key_0;
      @name(".NoAction") action NoAction_0() {
      }
      @name("MyIngress.set_data") action set_data_0() {
      }
      @name("MyIngress.t") table t {
          actions = {
              set_data_0();
