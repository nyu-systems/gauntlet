--- dumps/p4_16_samples/array-copy-bmv2.p4/pruned/array-copy-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:29:09.173200000 +0200
+++ dumps/p4_16_samples/array-copy-bmv2.p4/pruned/array-copy-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:29:09.229628500 +0200
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
