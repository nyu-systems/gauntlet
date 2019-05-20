*** dumps/p4_16_samples/pipe.p4/pruned/pipe-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 17:00:38.905012400 +0200
--- dumps/p4_16_samples/pipe.p4/pruned/pipe-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:00:38.910551100 +0200
*************** struct Packet_data {
*** 28,36 ****
  control Q_pipe(inout TArg1 qArg1, inout TArg2 qArg2) {
      TArg1 p1_tArg1_0;
      TArg2 p1_aArg2_0;
      @name(".NoAction") action NoAction_0() {
      }
-     bit<9> barg;
      @name("Q_pipe.p1.thost.B_action") action p1_thost_B_action(BParamType bData) {
          barg = bData;
          p1_tArg1_0.field1 = barg;
--- 28,36 ----
  control Q_pipe(inout TArg1 qArg1, inout TArg2 qArg2) {
      TArg1 p1_tArg1_0;
      TArg2 p1_aArg2_0;
+     bit<9> barg;
      @name(".NoAction") action NoAction_0() {
      }
      @name("Q_pipe.p1.thost.B_action") action p1_thost_B_action(BParamType bData) {
          barg = bData;
          p1_tArg1_0.field1 = barg;
