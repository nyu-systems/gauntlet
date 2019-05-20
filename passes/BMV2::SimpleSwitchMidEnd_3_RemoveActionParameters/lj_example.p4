*** dumps/p4_16_samples/lj_example.p4/pruned/lj_example-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:59:45.614166200 +0200
--- dumps/p4_16_samples/lj_example.p4/pruned/lj_example-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:59:45.586353400 +0200
*************** parser LJparse(packet_in b, out Parsed_r
*** 31,38 ****
      }
  }
  control LjPipe(inout Parsed_rep p, in error parseError, in InControl inCtrl, out OutControl outCtrl) {
!     @name("LjPipe.Drop_action") action Drop_action_0(out PortId port) {
          port = 4w0xf;
      }
      @name("LjPipe.Drop_1") action Drop() {
          outCtrl.outputPort = 4w0xf;
--- 31,40 ----
      }
  }
  control LjPipe(inout Parsed_rep p, in error parseError, in InControl inCtrl, out OutControl outCtrl) {
!     PortId port;
!     @name("LjPipe.Drop_action") action Drop_action_0() {
          port = 4w0xf;
+         outCtrl.outputPort = port;
      }
      @name("LjPipe.Drop_1") action Drop() {
          outCtrl.outputPort = 4w0xf;
*************** control LjPipe(inout Parsed_rep p, in er
*** 45,51 ****
              p.arpa_pak.dest: exact @name("p.arpa_pak.dest") ;
          }
          actions = {
!             Drop_action_0(outCtrl.outputPort);
              Drop();
              Forward_0();
          }
--- 47,53 ----
              p.arpa_pak.dest: exact @name("p.arpa_pak.dest") ;
          }
          actions = {
!             Drop_action_0();
              Drop();
              Forward_0();
          }
