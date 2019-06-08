--- dumps/pruned/array-copy-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:31:08.365669100 +0200
+++ dumps/pruned/array-copy-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:31:08.421687400 +0200
@@ -31,12 +31,10 @@ control egress(inout Headers h, inout Me
 }
 control deparser(packet_out b, in Headers h) {
     apply {
-        {
-            b.emit<Hdr>(h.h1[0]);
-            b.emit<Hdr>(h.h1[1]);
-            b.emit<Hdr>(h.h2[0]);
-            b.emit<Hdr>(h.h2[1]);
-        }
+        b.emit<Hdr>(h.h1[0]);
+        b.emit<Hdr>(h.h1[1]);
+        b.emit<Hdr>(h.h2[0]);
+        b.emit<Hdr>(h.h2[1]);
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
