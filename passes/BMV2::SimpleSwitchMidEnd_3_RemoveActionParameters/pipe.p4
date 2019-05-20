*** dumps/p4_16_samples/pipe.p4/pruned/pipe-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:00:38.933107500 +0200
--- dumps/p4_16_samples/pipe.p4/pruned/pipe-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:00:38.968492100 +0200
*************** extern bs {
*** 26,37 ****
  struct Packet_data {
  }
  control Q_pipe(inout TArg1 qArg1, inout TArg2 qArg2) {
-     @name(".NoAction") action NoAction_0() {
-     }
      TArg1 p1_tArg1_0;
      TArg2 p1_aArg2_0;
!     @name("Q_pipe.p1.thost.B_action") action p1_thost_B_action(out bit<9> barg, BParamType bData) {
          barg = bData;
      }
      @name("Q_pipe.p1.thost.C_action") action p1_thost_C_action(bit<9> cData) {
          p1_tArg1_0.field1 = cData;
--- 26,39 ----
  struct Packet_data {
  }
  control Q_pipe(inout TArg1 qArg1, inout TArg2 qArg2) {
      TArg1 p1_tArg1_0;
      TArg2 p1_aArg2_0;
!     @name(".NoAction") action NoAction_0() {
!     }
!     bit<9> barg;
!     @name("Q_pipe.p1.thost.B_action") action p1_thost_B_action(BParamType bData) {
          barg = bData;
+         p1_tArg1_0.field1 = barg;
      }
      @name("Q_pipe.p1.thost.C_action") action p1_thost_C_action(bit<9> cData) {
          p1_tArg1_0.field1 = cData;
*************** control Q_pipe(inout TArg1 qArg1, inout
*** 42,48 ****
              p1_aArg2_0.field2: exact @name("aArg2.field2") ;
          }
          actions = {
!             p1_thost_B_action(p1_tArg1_0.field1);
              p1_thost_C_action();
          }
          size = 32w5;
--- 44,50 ----
              p1_aArg2_0.field2: exact @name("aArg2.field2") ;
          }
          actions = {
!             p1_thost_B_action();
              p1_thost_C_action();
          }
          size = 32w5;
