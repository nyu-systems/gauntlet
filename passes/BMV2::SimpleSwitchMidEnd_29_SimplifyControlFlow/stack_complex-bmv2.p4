--- dumps/p4_16_samples/stack_complex-bmv2.p4/pruned/stack_complex-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:32:11.407799800 +0200
+++ dumps/p4_16_samples/stack_complex-bmv2.p4/pruned/stack_complex-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:32:11.412743600 +0200
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
