*** dumps/p4_16_samples/issue420.p4/pruned/issue420-BMV2::SimpleSwitchMidEnd_21_RemoveSelectBooleans.p4	2019-05-20 16:59:11.661003700 +0200
--- dumps/p4_16_samples/issue420.p4/pruned/issue420-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 16:59:11.663711000 +0200
*************** control cIngress(inout Parsed_packet hdr
*** 31,42 ****
      }
      @name("cIngress.foo") action foo_0(bit<16> bar) {
          hasReturned_1 = false;
!         if (bar == 16w0xf00d) {
!             hdr.ethernet.srcAddr = 48w0xdeadbeeff00d;
!             hasReturned_1 = true;
          }
-         if (!hasReturned_1) 
-             hdr.ethernet.srcAddr = 48w0x215241100ff2;
      }
      @name("cIngress.tbl1") table tbl1 {
          key = {
--- 31,57 ----
      }
      @name("cIngress.foo") action foo_0(bit<16> bar) {
          hasReturned_1 = false;
!         {
!             bool cond;
!             {
!                 bool pred;
!                 cond = bar == 16w0xf00d;
!                 pred = cond;
!                 {
!                     hdr.ethernet.srcAddr = (pred ? 48w0xdeadbeeff00d : hdr.ethernet.srcAddr);
!                     hasReturned_1 = (pred ? true : hasReturned_1);
!                 }
!             }
!         }
!         {
!             bool cond_0;
!             {
!                 bool pred_0;
!                 cond_0 = !hasReturned_1;
!                 pred_0 = cond_0;
!                 hdr.ethernet.srcAddr = (pred_0 ? 48w0x215241100ff2 : hdr.ethernet.srcAddr);
!             }
          }
      }
      @name("cIngress.tbl1") table tbl1 {
          key = {
