*** dumps/p4_16_samples/pipe.p4/pruned/pipe-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:00:38.915543900 +0200
--- dumps/p4_16_samples/pipe.p4/pruned/pipe-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:00:38.918333500 +0200
*************** struct Packet_data {
*** 28,39 ****
  control Q_pipe(inout TArg1 qArg1, inout TArg2 qArg2) {
      TArg1 p1_tArg1_0;
      TArg2 p1_aArg2_0;
-     bit<9> barg;
      @name(".NoAction") action NoAction_0() {
      }
      @name("Q_pipe.p1.thost.B_action") action p1_thost_B_action(BParamType bData) {
!         barg = bData;
!         p1_tArg1_0.field1 = barg;
      }
      @name("Q_pipe.p1.thost.C_action") action p1_thost_C_action(bit<9> cData) {
          p1_tArg1_0.field1 = cData;
--- 28,37 ----
  control Q_pipe(inout TArg1 qArg1, inout TArg2 qArg2) {
      TArg1 p1_tArg1_0;
      TArg2 p1_aArg2_0;
      @name(".NoAction") action NoAction_0() {
      }
      @name("Q_pipe.p1.thost.B_action") action p1_thost_B_action(BParamType bData) {
!         p1_tArg1_0.field1 = bData;
      }
      @name("Q_pipe.p1.thost.C_action") action p1_thost_C_action(bit<9> cData) {
          p1_tArg1_0.field1 = cData;
*************** control Q_pipe(inout TArg1 qArg1, inout
*** 55,61 ****
      }
      @name("Q_pipe.p1.Tinner") table p1_Tinner_0 {
          key = {
!             qArg1.field1: ternary @name("pArg1.field1") ;
          }
          actions = {
              p1_Drop();
--- 53,59 ----
      }
      @name("Q_pipe.p1.Tinner") table p1_Tinner_0 {
          key = {
!             p1_tArg1_0.field1: ternary @name("pArg1.field1") ;
          }
          actions = {
              p1_Drop();
*************** control Q_pipe(inout TArg1 qArg1, inout
*** 74,83 ****
          p1_thost_T_0.apply();
          {
              qArg1.field1 = p1_tArg1_0.field1;
-             qArg1.drop = p1_tArg1_0.drop;
          }
          {
-             p1_tArg1_0.field1 = qArg1.field1;
              p1_tArg1_0.drop = qArg1.drop;
          }
          {
--- 72,79 ----
*************** control Q_pipe(inout TArg1 qArg1, inout
*** 86,92 ****
          p1_thost_T_0.apply();
          {
              qArg1.field1 = p1_tArg1_0.field1;
-             qArg1.drop = p1_tArg1_0.drop;
          }
          p1_Tinner_0.apply();
      }
--- 82,87 ----
