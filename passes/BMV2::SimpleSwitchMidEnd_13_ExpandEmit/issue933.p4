--- dumps/pruned/issue933-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-06-08 18:32:48.880008700 +0200
+++ dumps/pruned/issue933-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:32:48.882710000 +0200
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
