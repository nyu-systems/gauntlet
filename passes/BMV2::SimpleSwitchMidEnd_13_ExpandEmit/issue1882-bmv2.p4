--- dumps/p4_16_samples/issue1882-bmv2.p4/pruned/issue1882-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:31:11.531677900 +0200
+++ dumps/p4_16_samples/issue1882-bmv2.p4/pruned/issue1882-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:31:11.534086800 +0200
@@ -25,7 +25,8 @@ control egress(inout Headers h, inout Me
 }
 control deparser(packet_out b, in Headers h) {
     apply {
-        b.emit<Headers>(h);
+        {
+        }
     }
 }
 extern ExternCounter {
