*** dumps/p4_16_samples/enum-bmv2.p4/pruned/enum-bmv2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:58:15.122167700 +0200
--- dumps/p4_16_samples/enum-bmv2.p4/pruned/enum-bmv2-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-05-20 16:58:15.125447100 +0200
*************** header hdr {
*** 5,14 ****
      bit<32> b;
      bit<32> c;
  }
- enum Choice {
-     First,
-     Second
- }
  struct Headers {
      hdr h;
  }
--- 5,10 ----
*************** control deparser(packet_out b, in Header
*** 38,47 ****
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
!     Choice c_c_0;
      apply {
!         c_c_0 = Choice.First;
!         if (c_c_0 == Choice.Second) 
              h.h.c = h.h.a;
          else 
              h.h.c = h.h.b;
--- 34,43 ----
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
!     bit<32> c_c_0;
      apply {
!         c_c_0 = 32w0;
!         if (c_c_0 == 32w1) 
              h.h.c = h.h.a;
          else 
              h.h.c = h.h.b;
