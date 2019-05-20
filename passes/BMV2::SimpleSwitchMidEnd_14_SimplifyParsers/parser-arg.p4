*** dumps/p4_16_samples/parser-arg.p4/pruned/parser-arg-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:59:53.359576700 +0200
--- dumps/p4_16_samples/parser-arg.p4/pruned/parser-arg-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 16:59:53.362997200 +0200
*************** parser Parser();
*** 3,25 ****
  package Package(Parser p1, Parser p2);
  parser Parser1_0() {
      state start {
-         transition Inside_start;
-     }
-     state Inside_start {
-         transition start_0;
-     }
-     state start_0 {
          transition accept;
      }
  }
  parser Parser2_0() {
      state start {
-         transition Inside_start_0;
-     }
-     state Inside_start_0 {
-         transition start_1;
-     }
-     state start_1 {
          transition accept;
      }
  }
--- 3,13 ----
