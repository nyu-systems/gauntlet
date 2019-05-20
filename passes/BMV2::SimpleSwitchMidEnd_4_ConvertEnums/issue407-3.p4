*** dumps/p4_16_samples/issue407-3.p4/pruned/issue407-3-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:59:10.908902800 +0200
--- dumps/p4_16_samples/issue407-3.p4/pruned/issue407-3-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-05-20 16:59:10.911096800 +0200
*************** struct mystruct2 {
*** 11,21 ****
      bit<4>    a;
      bit<4>    b;
  }
- enum myenum1 {
-     MY_ENUM1_VAL1,
-     MY_ENUM1_VAL2,
-     MY_ENUM1_VAL3
- }
  header Ethernet_h {
      EthernetAddress dstAddr;
      EthernetAddress srcAddr;
--- 11,16 ----
*************** struct myStruct1 {
*** 31,37 ****
      varbit<104>     x6;
      error           x7;
      bool            x8;
!     myenum1         x9;
      Ethernet_h      x10;
      Ethernet_h[4]   x11;
      mystruct1       x12;
--- 26,32 ----
      varbit<104>     x6;
      error           x7;
      bool            x8;
!     bit<32>         x9;
      Ethernet_h      x10;
      Ethernet_h[4]   x11;
      mystruct1       x12;
