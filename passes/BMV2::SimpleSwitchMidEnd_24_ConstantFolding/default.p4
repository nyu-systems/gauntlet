*** dumps/p4_16_samples/default.p4/pruned/default-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 16:58:11.684139900 +0200
--- dumps/p4_16_samples/default.p4/pruned/default-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:11.687660300 +0200
*************** parser p0(packet_in p, out Header h) {
*** 8,21 ****
          b = true;
          p.extract<Header>(h);
          transition select(h.data, (bit<1>)b) {
!             (default, (bit<1>)true): next;
              (default, default): reject;
          }
      }
      state next {
          p.extract<Header>(h);
          transition select(h.data, (bit<1>)b) {
!             (default, (bit<1>)true): accept;
              (default, default): reject;
              default: reject;
          }
--- 8,21 ----
          b = true;
          p.extract<Header>(h);
          transition select(h.data, (bit<1>)b) {
!             (default, 1w1): next;
              (default, default): reject;
          }
      }
      state next {
          p.extract<Header>(h);
          transition select(h.data, (bit<1>)b) {
!             (default, 1w1): accept;
              (default, default): reject;
              default: reject;
          }
