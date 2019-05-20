--- dumps/p4_16_samples/issue561-2-bmv2.p4/pruned/issue561-2-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:30:55.118651100 +0200
+++ dumps/p4_16_samples/issue561-2-bmv2.p4/pruned/issue561-2-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:30:55.121051700 +0200
@@ -69,7 +69,11 @@ control egress(inout headers hdr, inout
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
