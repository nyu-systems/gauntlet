*** dumps/p4_16_samples/issue407-3.p4/pruned/issue407-3-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 16:59:10.834827700 +0200
--- dumps/p4_16_samples/issue407-3.p4/pruned/issue407-3-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 16:59:10.837292100 +0200
*************** header Ethernet_h {
*** 16,22 ****
      EthernetAddress srcAddr;
      bit<16>         etherType;
  }
! typedef tuple<bit<8>, bit<16>> myTuple0;
  struct myStruct1 {
      bit<7>          x1;
      int<33>         x2;
--- 16,26 ----
      EthernetAddress srcAddr;
      bit<16>         etherType;
  }
! struct tuple_0 {
!     bit<8>  field;
!     bit<16> field_0;
! }
! typedef tuple_0 myTuple0;
  struct myStruct1 {
      bit<7>          x1;
      int<33>         x2;
