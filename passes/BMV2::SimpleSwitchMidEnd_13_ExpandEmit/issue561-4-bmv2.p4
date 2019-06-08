--- dumps/pruned/issue561-4-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-06-08 18:32:34.799704700 +0200
+++ dumps/pruned/issue561-4-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:32:34.803388300 +0200
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
