--- dumps/p4_16_samples/issue933.p4/pruned/issue933-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:31:14.268337000 +0200
+++ dumps/p4_16_samples/issue933.p4/pruned/issue933-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:31:14.322948100 +0200
@@ -5,8 +5,6 @@ struct headers {
 }
 control MyDeparser(packet_out packet, in headers hdr) {
     apply {
-        {
-        }
     }
 }
 Switch<headers>(MyDeparser()) main;
