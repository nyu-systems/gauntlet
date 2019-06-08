--- dumps/pruned/issue933-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:48.926805600 +0200
+++ dumps/pruned/issue933-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:48.961484900 +0200
@@ -5,8 +5,6 @@ struct headers {
 }
 control MyDeparser(packet_out packet, in headers hdr) {
     apply {
-        {
-        }
     }
 }
 Switch<headers>(MyDeparser()) main;
