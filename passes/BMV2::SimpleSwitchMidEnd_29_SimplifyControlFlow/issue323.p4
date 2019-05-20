--- dumps/p4_16_samples/issue323.p4/pruned/issue323-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:30:42.998545300 +0200
+++ dumps/p4_16_samples/issue323.p4/pruned/issue323-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:30:43.058757700 +0200
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
