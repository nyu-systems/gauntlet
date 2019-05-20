*** dumps/p4_16_samples/mux-bmv2.p4/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:59:47.521473300 +0200
--- dumps/p4_16_samples/mux-bmv2.p4/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:59:47.547895600 +0200
*************** control Eg(inout Headers hdrs, inout Met
*** 17,23 ****
      bit<32> _sub;
      bit<64> res;
      bit<32> tmp_0;
!     @name("Eg.update") action update_0(in bool p_1, inout bit<64> val) {
          _sub = val[31:0];
          if (p_1) 
              tmp_0 = _sub;
--- 17,27 ----
      bit<32> _sub;
      bit<64> res;
      bit<32> tmp_0;
!     bool p_1;
!     bit<64> val;
!     @name("Eg.update") action update_0() {
!         p_1 = true;
!         val = res;
          _sub = val[31:0];
          if (p_1) 
              tmp_0 = _sub;
*************** control Eg(inout Headers hdrs, inout Met
*** 25,34 ****
              tmp_0 = 32w1;
          _sub = tmp_0;
          val[31:0] = _sub;
      }
      apply {
          res = 64w0;
!         update_0(true, res);
      }
  }
  control DP(packet_out b, in Headers p) {
--- 29,39 ----
              tmp_0 = 32w1;
          _sub = tmp_0;
          val[31:0] = _sub;
+         res = val;
      }
      apply {
          res = 64w0;
!         update_0();
      }
  }
  control DP(packet_out b, in Headers p) {
