*** dumps/p4_16_samples/newtype.p4/pruned/newtype-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:59:49.867390700 +0200
--- dumps/p4_16_samples/newtype.p4/pruned/newtype-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:59:49.888139300 +0200
*************** header H {
*** 9,21 ****
      N32 field;
  }
  control c(out B32 x) {
-     @name(".NoAction") action NoAction_0() {
-     }
      N32 k;
      bit<32> b_1;
      N32 n_1;
      N32 n1;
      S s;
      @name("c.t") table t {
          actions = {
              NoAction_0();
--- 9,21 ----
      N32 field;
  }
  control c(out B32 x) {
      N32 k;
      bit<32> b_1;
      N32 n_1;
      N32 n1;
      S s;
+     @name(".NoAction") action NoAction_0() {
+     }
      @name("c.t") table t {
          actions = {
              NoAction_0();
