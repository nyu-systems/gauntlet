--- before_pass
+++ after_pass
@@ -38,7 +38,6 @@ control egress(inout headers hdr, inout
     }
 }
 control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
-    bool tmp;
     @name(".NoAction") action NoAction_0() {
     }
     @name("ingress.setDest") action setDest() {
@@ -55,7 +54,7 @@ control ingress(inout headers hdr, inout
         default_action = NoAction_0();
     }
     apply {
-        tmp = someTable_0.apply().hit;
+        someTable_0.apply();
     }
 }
 control DeparserImpl(packet_out packet, in headers hdr) {
