*** dumps/p4_16_samples/ternary2-bmv2.p4/pruned/ternary2-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:00:50.213320600 +0200
--- dumps/p4_16_samples/ternary2-bmv2.p4/pruned/ternary2-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:00:50.215827200 +0200
*************** control update(inout packet_t h, inout M
*** 40,50 ****
      }
  }
  control ingress(inout packet_t hdrs, inout Meta m, inout standard_metadata_t meta) {
-     bit<8> reg;
-     bit<8> reg_1;
-     bit<8> reg_2;
-     bit<8> reg_3;
-     bit<16> key_0;
      @name("ingress.setb1") action setb1_0(bit<9> port, bit<8> val) {
          hdrs.data.b1 = val;
          meta.egress_spec = port;
--- 40,45 ----
*************** control ingress(inout packet_t hdrs, ino
*** 60,79 ****
      @name("ingress.noop") action noop_8() {
      }
      @name("ingress.setbyte") action setbyte_0(bit<8> val) {
!         reg = val;
!         hdrs.extra[0].b1 = reg;
      }
      @name("ingress.setbyte") action setbyte_4(bit<8> val) {
!         reg_1 = val;
!         hdrs.data.b2 = reg_1;
      }
      @name("ingress.setbyte") action setbyte_5(bit<8> val) {
!         reg_2 = val;
!         hdrs.extra[1].b1 = reg_2;
      }
      @name("ingress.setbyte") action setbyte_6(bit<8> val) {
!         reg_3 = val;
!         hdrs.extra[2].b2 = reg_3;
      }
      @name("ingress.act1") action act1_0(bit<8> val) {
          hdrs.extra[0].b1 = val;
--- 55,70 ----
      @name("ingress.noop") action noop_8() {
      }
      @name("ingress.setbyte") action setbyte_0(bit<8> val) {
!         hdrs.extra[0].b1 = val;
      }
      @name("ingress.setbyte") action setbyte_4(bit<8> val) {
!         hdrs.data.b2 = val;
      }
      @name("ingress.setbyte") action setbyte_5(bit<8> val) {
!         hdrs.extra[1].b1 = val;
      }
      @name("ingress.setbyte") action setbyte_6(bit<8> val) {
!         hdrs.extra[2].b2 = val;
      }
      @name("ingress.act1") action act1_0(bit<8> val) {
          hdrs.extra[0].b1 = val;
*************** control ingress(inout packet_t hdrs, ino
*** 96,102 ****
      }
      @name("ingress.ex1") table ex1 {
          key = {
!             key_0: ternary @name("hdrs.extra[0].h") ;
          }
          actions = {
              setbyte_0();
--- 87,93 ----
      }
      @name("ingress.ex1") table ex1 {
          key = {
!             hdrs.extra[0].h: ternary @name("hdrs.extra[0].h") ;
          }
          actions = {
              setbyte_0();
*************** control ingress(inout packet_t hdrs, ino
*** 140,146 ****
      apply {
          test1.apply();
          {
-             key_0 = hdrs.extra[0].h;
              switch (ex1.apply().action_run) {
                  act1_0: {
                      tbl1.apply();
--- 131,136 ----
