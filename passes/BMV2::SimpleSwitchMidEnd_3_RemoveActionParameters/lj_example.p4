--- dumps/pruned/lj_example-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:32:56.242377100 +0200
+++ dumps/pruned/lj_example-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:32:56.223848200 +0200
@@ -31,8 +31,10 @@ parser LJparse(packet_in b, out Parsed_r
     }
 }
 control LjPipe(inout Parsed_rep p, in error parseError, in InControl inCtrl, out OutControl outCtrl) {
-    @name("LjPipe.Drop_action") action Drop_action_0(out PortId port) {
+    PortId port;
+    @name("LjPipe.Drop_action") action Drop_action_0() {
         port = 4w0xf;
+        outCtrl.outputPort = port;
     }
     @name("LjPipe.Drop_1") action Drop() {
         outCtrl.outputPort = 4w0xf;
@@ -45,7 +47,7 @@ control LjPipe(inout Parsed_rep p, in er
             p.arpa_pak.dest: exact @name("p.arpa_pak.dest") ;
         }
         actions = {
-            Drop_action_0(outCtrl.outputPort);
+            Drop_action_0();
             Drop();
             Forward_0();
         }
