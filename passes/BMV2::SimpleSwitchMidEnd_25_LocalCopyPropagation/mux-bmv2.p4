*** dumps/p4_16_samples/mux-bmv2.p4/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:47.508036500 +0200
--- dumps/p4_16_samples/mux-bmv2.p4/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:47.511446600 +0200
*************** control Ing(inout Headers headers, inout
*** 14,42 ****
      }
  }
  control Eg(inout Headers hdrs, inout Metadata meta, inout standard_metadata_t standard_meta) {
-     bit<32> _sub;
      bit<64> res;
      bit<32> tmp_0;
-     bool p_1;
      bit<64> val;
-     bool cond;
-     bool pred;
      @name("Eg.update") action update_0() {
-         p_1 = true;
          val = res;
-         _sub = val[31:0];
          {
              {
!                 cond = p_1;
!                 pred = cond;
!                 tmp_0 = (pred ? _sub : tmp_0);
!                 cond = !cond;
!                 pred = cond;
!                 tmp_0 = (pred ? 32w1 : tmp_0);
              }
          }
!         _sub = tmp_0;
!         val[31:0] = _sub;
          res = val;
      }
      apply {
--- 14,31 ----
      }
  }
  control Eg(inout Headers hdrs, inout Metadata meta, inout standard_metadata_t standard_meta) {
      bit<64> res;
      bit<32> tmp_0;
      bit<64> val;
      @name("Eg.update") action update_0() {
          val = res;
          {
              {
!                 tmp_0 = (true ? res[31:0] : tmp_0);
!                 tmp_0 = (!true ? 32w1 : tmp_0);
              }
          }
!         val[31:0] = tmp_0;
          res = val;
      }
      apply {
