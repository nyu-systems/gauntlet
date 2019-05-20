--- dumps/p4_16_samples/lj_example.p4/pruned/lj_example-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:31:22.813765300 +0200
+++ dumps/p4_16_samples/lj_example.p4/pruned/lj_example-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:31:22.816297500 +0200
@@ -31,10 +31,8 @@ parser LJparse(packet_in b, out Parsed_r
     }
 }
 control LjPipe(inout Parsed_rep p, in error parseError, in InControl inCtrl, out OutControl outCtrl) {
-    PortId port;
     @name("LjPipe.Drop_action") action Drop_action_0() {
-        port = 4w0xf;
-        outCtrl.outputPort = port;
+        outCtrl.outputPort = 4w0xf;
     }
     @name("LjPipe.Drop_1") action Drop() {
         outCtrl.outputPort = 4w0xf;
