*** dumps/p4_16_samples/issue696-bmv2.p4/pruned/issue696-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:25.572034800 +0200
--- dumps/p4_16_samples/issue696-bmv2.p4/pruned/issue696-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:25.635212000 +0200
*************** control Eg(inout Headers hdrs, inout Met
*** 55,76 ****
      bit<32> tmp_1;
      bit<32> tmp_2;
      @name("Eg.test") action test_0() {
!         {
!             val.field1 = 32w0;
!         }
!         {
!             {
!                 tmp_1 = tmp_1;
!                 tmp_1 = 32w0;
!             }
!         }
          inc = tmp_1;
!         {
!             {
!                 tmp_2 = tmp_2;
!                 tmp_2 = 32w0;
!             }
!         }
          debug.write(32w0, tmp_2);
          debug.write(32w1, inc);
          val.field1 = 32w1;
--- 55,66 ----
      bit<32> tmp_1;
      bit<32> tmp_2;
      @name("Eg.test") action test_0() {
!         val.field1 = 32w0;
!         tmp_1 = tmp_1;
!         tmp_1 = 32w0;
          inc = tmp_1;
!         tmp_2 = tmp_2;
!         tmp_2 = 32w0;
          debug.write(32w0, tmp_2);
          debug.write(32w1, inc);
          val.field1 = 32w1;
