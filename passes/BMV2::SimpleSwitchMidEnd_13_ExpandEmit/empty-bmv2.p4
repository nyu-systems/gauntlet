--- dumps/p4_16_samples/empty-bmv2.p4/pruned/empty-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:29:37.610805700 +0200
+++ dumps/p4_16_samples/empty-bmv2.p4/pruned/empty-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:29:37.615074800 +0200
@@ -25,7 +25,8 @@ control egress(inout Headers h, inout Me
 }
 control deparser(packet_out b, in Headers h) {
     apply {
-        b.emit<Headers>(h);
+        {
+        }
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
