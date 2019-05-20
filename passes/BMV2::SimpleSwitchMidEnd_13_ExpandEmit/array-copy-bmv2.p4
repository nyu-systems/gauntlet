--- dumps/p4_16_samples/array-copy-bmv2.p4/pruned/array-copy-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:29:09.131188400 +0200
+++ dumps/p4_16_samples/array-copy-bmv2.p4/pruned/array-copy-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:29:09.133574100 +0200
@@ -31,7 +31,12 @@ control egress(inout Headers h, inout Me
 }
 control deparser(packet_out b, in Headers h) {
     apply {
-        b.emit<Headers>(h);
+        {
+            b.emit<Hdr>(h.h1[0]);
+            b.emit<Hdr>(h.h1[1]);
+            b.emit<Hdr>(h.h2[0]);
+            b.emit<Hdr>(h.h2[1]);
+        }
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
