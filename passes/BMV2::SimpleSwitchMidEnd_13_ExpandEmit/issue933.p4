--- dumps/p4_16_samples/issue933.p4/pruned/issue933-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:31:14.220943100 +0200
+++ dumps/p4_16_samples/issue933.p4/pruned/issue933-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:31:14.223164200 +0200
@@ -5,7 +5,8 @@ struct headers {
 }
 control MyDeparser(packet_out packet, in headers hdr) {
     apply {
-        packet.emit<headers>({  });
+        {
+        }
     }
 }
 Switch<headers>(MyDeparser()) main;
