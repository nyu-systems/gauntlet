*** dumps/p4_16_samples/issue1806.p4/pruned/issue1806-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 16:58:57.802121500 +0200
--- dumps/p4_16_samples/issue1806.p4/pruned/issue1806-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 16:58:57.804821300 +0200
*************** parser prs(packet_in p, out Headers h) {
*** 14,24 ****
      }
  }
  control c(inout Headers h, inout standard_metadata_t sm) {
      @name(".NoAction") action NoAction_0() {
      }
      @name("c.do_act") action do_act_0() {
      }
-     bit<10> key_0;
      @name("c.tns") table tns {
          key = {
              key_0: exact @name("h.eth.tst[13:4]") ;
--- 14,24 ----
      }
  }
  control c(inout Headers h, inout standard_metadata_t sm) {
+     bit<10> key_0;
      @name(".NoAction") action NoAction_0() {
      }
      @name("c.do_act") action do_act_0() {
      }
      @name("c.tns") table tns {
          key = {
              key_0: exact @name("h.eth.tst[13:4]") ;
