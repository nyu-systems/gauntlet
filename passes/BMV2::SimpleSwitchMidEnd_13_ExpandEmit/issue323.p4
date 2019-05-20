--- dumps/p4_16_samples/issue323.p4/pruned/issue323-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:30:42.934063800 +0200
+++ dumps/p4_16_samples/issue323.p4/pruned/issue323-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:30:42.937706600 +0200
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
