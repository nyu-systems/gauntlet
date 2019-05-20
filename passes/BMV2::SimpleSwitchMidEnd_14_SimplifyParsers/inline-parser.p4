*** dumps/p4_16_samples/inline-parser.p4/pruned/inline-parser-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:58:34.182691600 +0200
--- dumps/p4_16_samples/inline-parser.p4/pruned/inline-parser-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 16:58:34.185078800 +0200
*************** parser p1(packet_in p, out Header[2] h)
*** 6,27 ****
      Header h_1;
      state start {
          h_1.setInvalid();
-         transition p0_start;
-     }
-     state p0_start {
          p.extract<Header>(h_1);
-         transition start_0;
-     }
-     state start_0 {
          h[0] = h_1;
          h_1.setInvalid();
-         transition p0_start_0;
-     }
-     state p0_start_0 {
          p.extract<Header>(h_1);
-         transition start_1;
-     }
-     state start_1 {
          h[1] = h_1;
          transition accept;
      }
--- 6,15 ----
