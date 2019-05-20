*** dumps/p4_16_samples/mux-bmv2.p4/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_21_RemoveSelectBooleans.p4	2019-05-20 16:59:47.498129800 +0200
--- dumps/p4_16_samples/mux-bmv2.p4/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 16:59:47.500745700 +0200
*************** control Eg(inout Headers hdrs, inout Met
*** 23,32 ****
          p_1 = true;
          val = res;
          _sub = val[31:0];
!         if (p_1) 
!             tmp_0 = _sub;
!         else 
!             tmp_0 = 32w1;
          _sub = tmp_0;
          val[31:0] = _sub;
          res = val;
--- 23,40 ----
          p_1 = true;
          val = res;
          _sub = val[31:0];
!         {
!             bool cond;
!             {
!                 bool pred;
!                 cond = p_1;
!                 pred = cond;
!                 tmp_0 = (pred ? _sub : tmp_0);
!                 cond = !cond;
!                 pred = cond;
!                 tmp_0 = (pred ? 32w1 : tmp_0);
!             }
!         }
          _sub = tmp_0;
          val[31:0] = _sub;
          res = val;
