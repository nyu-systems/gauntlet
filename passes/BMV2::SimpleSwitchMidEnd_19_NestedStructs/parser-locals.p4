*** dumps/p4_16_samples/parser-locals.p4/pruned/parser-locals-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:59:53.983621300 +0200
--- dumps/p4_16_samples/parser-locals.p4/pruned/parser-locals-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-05-20 16:59:53.986084900 +0200
*************** struct S {
*** 9,18 ****
      bit<32> c;
  }
  parser p() {
!     S s;
      state start {
!         s.h1.setInvalid();
!         s.h2.setInvalid();
          transition accept;
      }
  }
--- 9,20 ----
      bit<32> c;
  }
  parser p() {
!     H s_h1;
!     H s_h2;
!     bit<32> s_c;
      state start {
!         s_h1.setInvalid();
!         s_h2.setInvalid();
          transition accept;
      }
  }
