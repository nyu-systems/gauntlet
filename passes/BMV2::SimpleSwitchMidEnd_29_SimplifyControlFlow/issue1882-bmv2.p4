--- dumps/p4_16_samples/issue1882-bmv2.p4/pruned/issue1882-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:31:11.582611600 +0200
+++ dumps/p4_16_samples/issue1882-bmv2.p4/pruned/issue1882-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:31:11.638054800 +0200
@@ -25,8 +25,6 @@ control egress(inout Headers h, inout Me
 }
 control deparser(packet_out b, in Headers h) {
     apply {
-        {
-        }
     }
 }
 extern ExternCounter {
