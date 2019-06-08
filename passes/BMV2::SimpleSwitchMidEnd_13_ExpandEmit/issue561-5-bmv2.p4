--- dumps/pruned/issue561-5-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-06-08 18:32:35.623345500 +0200
+++ dumps/pruned/issue561-5-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:32:35.627846600 +0200
@@ -65,7 +65,10 @@ control egress(inout headers hdr, inout
 }
 control DeparserImpl(packet_out packet, in headers hdr) {
     apply {
-        packet.emit<headers>(hdr);
+        {
+            packet.emit<S>(hdr.base);
+            packet.emit<U>(hdr.u[0]);
+        }
     }
 }
 control verifyChecksum(inout headers hdr, inout metadata meta) {
