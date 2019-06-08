--- dumps/pruned/issue561-1-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-06-08 18:32:33.390969100 +0200
+++ dumps/pruned/issue561-1-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:32:33.393150500 +0200
@@ -66,7 +66,11 @@ control egress(inout headers hdr, inout
 }
 control DeparserImpl(packet_out packet, in headers hdr) {
     apply {
-        packet.emit<headers>(hdr);
+        {
+            packet.emit<S>(hdr.base);
+            packet.emit<O1>(hdr.u.byte);
+            packet.emit<O2>(hdr.u.short);
+        }
     }
 }
 control verifyChecksum(inout headers hdr, inout metadata meta) {
