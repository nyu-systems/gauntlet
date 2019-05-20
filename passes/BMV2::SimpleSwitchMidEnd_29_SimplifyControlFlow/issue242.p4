*** dumps/p4_16_samples/issue242.p4/pruned/issue242-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:02.986372300 +0200
--- dumps/p4_16_samples/issue242.p4/pruned/issue242-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:03.050447200 +0200
*************** control Eg(inout Headers hdrs, inout Met
*** 55,76 ****
      @name("Eg.debug") register<bit<32>>(32w100) debug;
      @name("Eg.reg") register<bit<32>>(32w1) reg;
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
      @name("Eg.debug") register<bit<32>>(32w100) debug;
      @name("Eg.reg") register<bit<32>>(32w1) reg;
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
