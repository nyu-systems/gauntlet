*** dumps/p4_16_samples/issue512.p4/pruned/issue512-BMV2::SimpleSwitchMidEnd_21_RemoveSelectBooleans.p4	2019-05-20 16:59:17.358145700 +0200
--- dumps/p4_16_samples/issue512.p4/pruned/issue512-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 16:59:17.362156800 +0200
*************** control cIngress(inout Parsed_packet hdr
*** 29,40 ****
      @name("cIngress.foo") action foo_0() {
          hasReturned_0 = false;
          meta.b = meta.b + 4w5;
!         if (meta.b > 4w10) {
!             meta.b = meta.b ^ 4w5;
!             hasReturned_0 = true;
          }
-         if (!hasReturned_0) 
-             meta.b = meta.b + 4w5;
      }
      @name("cIngress.guh") table guh {
          key = {
--- 29,55 ----
      @name("cIngress.foo") action foo_0() {
          hasReturned_0 = false;
          meta.b = meta.b + 4w5;
!         {
!             bool cond;
!             {
!                 bool pred;
!                 cond = meta.b > 4w10;
!                 pred = cond;
!                 {
!                     meta.b = (pred ? meta.b ^ 4w5 : meta.b);
!                     hasReturned_0 = (pred ? true : hasReturned_0);
!                 }
!             }
!         }
!         {
!             bool cond_0;
!             {
!                 bool pred_0;
!                 cond_0 = !hasReturned_0;
!                 pred_0 = cond_0;
!                 meta.b = (pred_0 ? meta.b + 4w5 : meta.b);
!             }
          }
      }
      @name("cIngress.guh") table guh {
          key = {
