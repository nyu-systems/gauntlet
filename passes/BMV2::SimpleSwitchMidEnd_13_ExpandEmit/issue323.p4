--- dumps/pruned/issue323-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-06-08 18:32:23.046046800 +0200
+++ dumps/pruned/issue323-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:32:23.047989500 +0200
@@ -28,7 +28,9 @@ control egress(inout Headers h, inout Me
 }
 control deparser(packet_out b, in Headers h) {
     apply {
-        b.emit<Headers>(h);
+        {
+            b.emit<hdr>(h.h);
+        }
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
