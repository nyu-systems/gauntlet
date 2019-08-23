--- before_pass
+++ after_pass
@@ -90,6 +90,7 @@ parser parserI(packet_in pkt, out header
     }
 }
 control cIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
+    bit<16> key_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name(".NoAction") action NoAction_4() {
@@ -138,7 +139,6 @@ control cIngress(inout headers hdr, inou
         size = 8;
         default_action = NoAction_4();
     }
-    bit<16> key_0;
     @name("cIngress.t2") table t2_0 {
         actions = {
             foo1_4();
