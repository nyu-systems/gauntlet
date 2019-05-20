*** dumps/p4_16_samples/ternary2-bmv2.p4/pruned/ternary2-bmv2-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:00:50.230073800 +0200
--- dumps/p4_16_samples/ternary2-bmv2.p4/pruned/ternary2-bmv2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:00:50.259698700 +0200
*************** control ingress(inout packet_t hdrs, ino
*** 54,70 ****
      }
      @name("ingress.noop") action noop_8() {
      }
!     @name("ingress.setbyte") action setbyte_0(out bit<8> reg, bit<8> val) {
          reg = val;
      }
!     @name("ingress.setbyte") action setbyte_4(out bit<8> reg_1, bit<8> val) {
          reg_1 = val;
      }
!     @name("ingress.setbyte") action setbyte_5(out bit<8> reg_2, bit<8> val) {
          reg_2 = val;
      }
!     @name("ingress.setbyte") action setbyte_6(out bit<8> reg_3, bit<8> val) {
          reg_3 = val;
      }
      @name("ingress.act1") action act1_0(bit<8> val) {
          hdrs.extra[0].b1 = val;
--- 54,78 ----
      }
      @name("ingress.noop") action noop_8() {
      }
!     bit<8> reg;
!     @name("ingress.setbyte") action setbyte_0(bit<8> val) {
          reg = val;
+         hdrs.extra[0].b1 = reg;
      }
!     bit<8> reg_1;
!     @name("ingress.setbyte") action setbyte_4(bit<8> val) {
          reg_1 = val;
+         hdrs.data.b2 = reg_1;
      }
!     bit<8> reg_2;
!     @name("ingress.setbyte") action setbyte_5(bit<8> val) {
          reg_2 = val;
+         hdrs.extra[1].b1 = reg_2;
      }
!     bit<8> reg_3;
!     @name("ingress.setbyte") action setbyte_6(bit<8> val) {
          reg_3 = val;
+         hdrs.extra[2].b2 = reg_3;
      }
      @name("ingress.act1") action act1_0(bit<8> val) {
          hdrs.extra[0].b1 = val;
*************** control ingress(inout packet_t hdrs, ino
*** 90,96 ****
              hdrs.extra[0].h: ternary @name("hdrs.extra[0].h") ;
          }
          actions = {
!             setbyte_0(hdrs.extra[0].b1);
              act1_0();
              act2_0();
              act3_0();
--- 98,104 ----
              hdrs.extra[0].h: ternary @name("hdrs.extra[0].h") ;
          }
          actions = {
!             setbyte_0();
              act1_0();
              act2_0();
              act3_0();
*************** control ingress(inout packet_t hdrs, ino
*** 103,109 ****
              hdrs.data.f2: ternary @name("hdrs.data.f2") ;
          }
          actions = {
!             setbyte_4(hdrs.data.b2);
              noop_6();
          }
          default_action = noop_6();
--- 111,117 ----
              hdrs.data.f2: ternary @name("hdrs.data.f2") ;
          }
          actions = {
!             setbyte_4();
              noop_6();
          }
          default_action = noop_6();
*************** control ingress(inout packet_t hdrs, ino
*** 113,119 ****
              hdrs.data.f2: ternary @name("hdrs.data.f2") ;
          }
          actions = {
!             setbyte_5(hdrs.extra[1].b1);
              noop_7();
          }
          default_action = noop_7();
--- 121,127 ----
              hdrs.data.f2: ternary @name("hdrs.data.f2") ;
          }
          actions = {
!             setbyte_5();
              noop_7();
          }
          default_action = noop_7();
*************** control ingress(inout packet_t hdrs, ino
*** 123,129 ****
              hdrs.data.f2: ternary @name("hdrs.data.f2") ;
          }
          actions = {
!             setbyte_6(hdrs.extra[2].b2);
              noop_8();
          }
          default_action = noop_8();
--- 131,137 ----
              hdrs.data.f2: ternary @name("hdrs.data.f2") ;
          }
          actions = {
!             setbyte_6();
              noop_8();
          }
          default_action = noop_8();
