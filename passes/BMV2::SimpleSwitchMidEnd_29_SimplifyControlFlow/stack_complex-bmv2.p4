--- dumps/pruned/stack_complex-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:34:02.496279500 +0200
+++ dumps/pruned/stack_complex-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:34:02.498188400 +0200
@@ -35,11 +35,9 @@ control egress(inout Headers h, inout Me
 }
 control deparser(packet_out b, in Headers h) {
     apply {
-        {
-            b.emit<hdr>(h.hs[0]);
-            b.emit<hdr>(h.hs[1]);
-            b.emit<hdr>(h.hs[2]);
-        }
+        b.emit<hdr>(h.hs[0]);
+        b.emit<hdr>(h.hs[1]);
+        b.emit<hdr>(h.hs[2]);
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
