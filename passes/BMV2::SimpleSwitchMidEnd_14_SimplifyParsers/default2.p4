*** dumps/p4_16_samples/default2.p4/pruned/default2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:58:11.926382200 +0200
--- dumps/p4_16_samples/default2.p4/pruned/default2-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 16:58:11.930396700 +0200
*************** header Header {
*** 5,13 ****
  parser p0(packet_in p, out Header h) {
      state start {
          p.extract<Header>(h);
-         transition next;
-     }
-     state next {
          transition accept;
      }
  }
--- 5,10 ----
