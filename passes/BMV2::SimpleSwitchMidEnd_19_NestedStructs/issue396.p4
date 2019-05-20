*** dumps/p4_16_samples/issue396.p4/pruned/issue396-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:59:10.176644900 +0200
--- dumps/p4_16_samples/issue396.p4/pruned/issue396-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-05-20 16:59:10.255009700 +0200
*************** package top(c _c);
*** 9,16 ****
  control d(out bool b) {
      H h_1;
      H[2] h3;
!     S s;
!     S s1;
      bool eout;
      H tmp_0;
      apply {
--- 9,16 ----
  control d(out bool b) {
      H h_1;
      H[2] h3;
!     H s_h;
!     H s1_h;
      bool eout;
      H tmp_0;
      apply {
*************** control d(out bool b) {
*** 18,27 ****
          {
              h_1.x = 32w0;
          }
!         s.h.setValid();
!         s1.h.setValid();
          {
!             s1.h.x = 32w0;
          }
          h3[0].setValid();
          h3[1].setValid();
--- 18,27 ----
          {
              h_1.x = 32w0;
          }
!         s_h.setValid();
!         s1_h.setValid();
          {
!             s1_h.x = 32w0;
          }
          h3[0].setValid();
          h3[1].setValid();
*************** control d(out bool b) {
*** 33,39 ****
              tmp_0.x = 32w0;
          }
          eout = tmp_0.isValid();
!         b = h_1.isValid() && eout && h3[1].isValid() && s1.h.isValid();
      }
  }
  top(d()) main;
--- 33,39 ----
              tmp_0.x = 32w0;
          }
          eout = tmp_0.isValid();
!         b = h_1.isValid() && eout && h3[1].isValid() && s1_h.isValid();
      }
  }
  top(d()) main;
