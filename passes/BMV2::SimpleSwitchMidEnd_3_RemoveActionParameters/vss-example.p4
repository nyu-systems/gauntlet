*** dumps/p4_16_samples/vss-example.p4/pruned/vss-example-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:01:00.630974600 +0200
--- dumps/p4_16_samples/vss-example.p4/pruned/vss-example-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:01:00.598313100 +0200
*************** parser TopParser(packet_in b, out Parsed
*** 71,79 ****
      }
  }
  control TopPipe(inout Parsed_packet headers, in error parseError, in InControl inCtrl, out OutControl outCtrl) {
      @name(".NoAction") action NoAction_0() {
      }
-     IPv4Address nextHop;
      @name("TopPipe.Drop_action") action Drop_action_0() {
          outCtrl.outputPort = 4w0xf;
      }
--- 71,80 ----
      }
  }
  control TopPipe(inout Parsed_packet headers, in error parseError, in InControl inCtrl, out OutControl outCtrl) {
+     IPv4Address nextHop;
+     bool hasReturned_0;
      @name(".NoAction") action NoAction_0() {
      }
      @name("TopPipe.Drop_action") action Drop_action_0() {
          outCtrl.outputPort = 4w0xf;
      }
*************** control TopPipe(inout Parsed_packet head
*** 144,150 ****
          default_action = Drop_action_5();
      }
      apply {
!         bool hasReturned_0 = false;
          if (parseError != error.NoError) {
              Drop_action_6();
              hasReturned_0 = true;
--- 145,151 ----
          default_action = Drop_action_5();
      }
      apply {
!         hasReturned_0 = false;
          if (parseError != error.NoError) {
              Drop_action_6();
              hasReturned_0 = true;
