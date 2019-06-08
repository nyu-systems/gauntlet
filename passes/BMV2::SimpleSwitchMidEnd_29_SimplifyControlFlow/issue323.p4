--- dumps/pruned/issue323-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:23.082001400 +0200
+++ dumps/pruned/issue323-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:23.123027500 +0200
@@ -28,9 +28,7 @@ control egress(inout Headers h, inout Me
 }
 control deparser(packet_out b, in Headers h) {
     apply {
-        {
-            b.emit<hdr>(h.h);
-        }
+        b.emit<hdr>(h.h);
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
