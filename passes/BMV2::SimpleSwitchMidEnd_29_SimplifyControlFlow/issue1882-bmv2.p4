--- dumps/pruned/issue1882-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:46.783915700 +0200
+++ dumps/pruned/issue1882-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:46.847079700 +0200
@@ -25,8 +25,6 @@ control egress(inout Headers h, inout Me
 }
 control deparser(packet_out b, in Headers h) {
     apply {
-        {
-        }
     }
 }
 extern ExternCounter {
