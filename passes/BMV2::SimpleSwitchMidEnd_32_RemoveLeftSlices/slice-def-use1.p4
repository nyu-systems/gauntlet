*** dumps/p4_16_samples/slice-def-use1.p4/pruned/slice-def-use1-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-05-20 17:00:23.061135000 +0200
--- dumps/p4_16_samples/slice-def-use1.p4/pruned/slice-def-use1-BMV2::SimpleSwitchMidEnd_32_RemoveLeftSlices.p4	2019-05-20 17:00:23.063498400 +0200
*************** control Ing(inout Headers headers, inout
*** 37,43 ****
      @name("Ing.debug") register<bit<8>>(32w2) debug;
      @name("Ing.act") action act_0() {
          n = 8w0b11111111;
!         n[7:4] = 4w0;
          debug.write(32w1, n);
          standard_meta.egress_spec = 9w0;
      }
--- 37,43 ----
      @name("Ing.debug") register<bit<8>>(32w2) debug;
      @name("Ing.act") action act_0() {
          n = 8w0b11111111;
!         n = n & ~8w0xf0 | (bit<8>)4w0 << 4 & 8w0xf0;
          debug.write(32w1, n);
          standard_meta.egress_spec = 9w0;
      }
