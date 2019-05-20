*** dumps/p4_16_samples/lj_example.p4/pruned/lj_example-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:45.546305100 +0200
--- dumps/p4_16_samples/lj_example.p4/pruned/lj_example-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:45.549465200 +0200
*************** parser LJparse(packet_in b, out Parsed_r
*** 31,40 ****
      }
  }
  control LjPipe(inout Parsed_rep p, in error parseError, in InControl inCtrl, out OutControl outCtrl) {
-     PortId port;
      @name("LjPipe.Drop_action") action Drop_action_0() {
!         port = 4w0xf;
!         outCtrl.outputPort = port;
      }
      @name("LjPipe.Drop_1") action Drop() {
          outCtrl.outputPort = 4w0xf;
--- 31,38 ----
      }
  }
  control LjPipe(inout Parsed_rep p, in error parseError, in InControl inCtrl, out OutControl outCtrl) {
      @name("LjPipe.Drop_action") action Drop_action_0() {
!         outCtrl.outputPort = 4w0xf;
      }
      @name("LjPipe.Drop_1") action Drop() {
          outCtrl.outputPort = 4w0xf;
