*** dumps/p4_16_samples/default2.p4/pruned/default2-BMV2::SimpleSwitchMidEnd_10_StrengthReduction.p4	2019-05-20 16:58:11.919196000 +0200
--- dumps/p4_16_samples/default2.p4/pruned/default2-BMV2::SimpleSwitchMidEnd_11_SimplifySelectCases.p4	2019-05-20 16:58:11.921553400 +0200
*************** header Header {
*** 5,14 ****
  parser p0(packet_in p, out Header h) {
      state start {
          p.extract<Header>(h);
!         transition select(h.data) {
!             default: next;
!             default: reject;
!         }
      }
      state next {
          transition accept;
--- 5,11 ----
  parser p0(packet_in p, out Header h) {
      state start {
          p.extract<Header>(h);
!         transition next;
      }
      state next {
          transition accept;
