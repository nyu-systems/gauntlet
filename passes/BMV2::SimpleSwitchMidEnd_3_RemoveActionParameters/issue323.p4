*** dumps/p4_16_samples/issue323.p4/pruned/issue323-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:59:07.970325300 +0200
--- dumps/p4_16_samples/issue323.p4/pruned/issue323-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:59:07.997470900 +0200
*************** control deparser(packet_out b, in Header
*** 32,46 ****
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
!     @name("ingress.my_a") action my_a_0(bit<32> v) {
          h.h.f = v;
      }
!     @name("ingress.my_a") action my_a_2(bit<32> v_1) {
          h.h.f = v_1;
      }
      apply {
!         my_a_0(32w0);
!         my_a_2(32w1);
      }
  }
  V1Switch<Headers, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
--- 32,50 ----
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
!     bit<32> v;
!     @name("ingress.my_a") action my_a_0() {
!         v = 32w0;
          h.h.f = v;
      }
!     bit<32> v_1;
!     @name("ingress.my_a") action my_a_2() {
!         v_1 = 32w1;
          h.h.f = v_1;
      }
      apply {
!         my_a_0();
!         my_a_2();
      }
  }
  V1Switch<Headers, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
