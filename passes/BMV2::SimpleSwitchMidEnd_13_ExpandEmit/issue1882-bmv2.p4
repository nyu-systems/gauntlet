--- dumps/pruned/issue1882-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-06-08 18:32:46.696285600 +0200
+++ dumps/pruned/issue1882-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:32:46.710296300 +0200
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
