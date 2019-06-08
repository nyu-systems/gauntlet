--- before_pass
+++ after_pass
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
