--- dumps/pruned/lj_example-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:32:56.192980300 +0200
+++ dumps/pruned/lj_example-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:56.196790500 +0200
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
