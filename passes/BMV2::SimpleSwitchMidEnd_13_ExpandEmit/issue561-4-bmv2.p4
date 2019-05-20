--- dumps/p4_16_samples/issue561-4-bmv2.p4/pruned/issue561-4-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:30:56.233853400 +0200
+++ dumps/p4_16_samples/issue561-4-bmv2.p4/pruned/issue561-4-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:30:56.238390600 +0200
@@ -85,7 +85,11 @@ control egress(inout headers hdr, inout
 }
 control DeparserImpl(packet_out packet, in headers hdr) {
     apply {
-        packet.emit<headers>(hdr);
+        {
+            packet.emit<S>(hdr.base);
+            packet.emit<U>(hdr.u[0]);
+            packet.emit<U>(hdr.u[1]);
+        }
     }
 }
 control verifyChecksum(inout headers hdr, inout metadata meta) {
