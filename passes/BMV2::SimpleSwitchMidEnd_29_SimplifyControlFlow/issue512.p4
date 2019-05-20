*** dumps/p4_16_samples/issue512.p4/pruned/issue512-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:17.379539800 +0200
--- dumps/p4_16_samples/issue512.p4/pruned/issue512-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:17.435771600 +0200
*************** control cIngress(inout Parsed_packet hdr
*** 28,46 ****
      bool pred;
      @name("cIngress.foo") action foo_0() {
          meta.b = meta.b + 4w5;
!         {
!             {
!                 pred = meta.b > 4w10;
!                 {
!                     meta.b = (meta.b > 4w10 ? meta.b ^ 4w5 : meta.b);
!                 }
!             }
!         }
!         {
!             {
!                 meta.b = (!(pred ? true : false) ? meta.b + 4w5 : meta.b);
!             }
!         }
      }
      @name("cIngress.guh") table guh {
          key = {
--- 28,36 ----
      bool pred;
      @name("cIngress.foo") action foo_0() {
          meta.b = meta.b + 4w5;
!         pred = meta.b > 4w10;
!         meta.b = (meta.b > 4w10 ? meta.b ^ 4w5 : meta.b);
!         meta.b = (!(pred ? true : false) ? meta.b + 4w5 : meta.b);
      }
      @name("cIngress.guh") table guh {
          key = {
