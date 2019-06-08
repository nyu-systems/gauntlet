--- dumps/pruned/empty-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:31:33.052954400 +0200
+++ dumps/pruned/empty-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:31:33.054917100 +0200
@@ -25,8 +25,6 @@ control egress(inout Headers h, inout Me
 }
 control deparser(packet_out b, in Headers h) {
     apply {
-        {
-        }
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
