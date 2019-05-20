--- dumps/p4_16_samples/issue561-3-bmv2.p4/pruned/issue561-3-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:30:55.564512300 +0200
+++ dumps/p4_16_samples/issue561-3-bmv2.p4/pruned/issue561-3-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:30:55.566404500 +0200
@@ -75,7 +75,11 @@ control egress(inout headers hdr, inout
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
