--- dumps/p4_16_samples/stack_complex-bmv2.p4/pruned/stack_complex-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:32:11.271373600 +0200
+++ dumps/p4_16_samples/stack_complex-bmv2.p4/pruned/stack_complex-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:32:11.274941900 +0200
@@ -35,7 +35,11 @@ control egress(inout Headers h, inout Me
 }
 control deparser(packet_out b, in Headers h) {
     apply {
-        b.emit<hdr[3]>(h.hs);
+        {
+            b.emit<hdr>(h.hs[0]);
+            b.emit<hdr>(h.hs[1]);
+            b.emit<hdr>(h.hs[2]);
+        }
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
