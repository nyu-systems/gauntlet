--- dumps/p4_16_samples/issue561-5-bmv2.p4/pruned/issue561-5-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:30:56.680928900 +0200
+++ dumps/p4_16_samples/issue561-5-bmv2.p4/pruned/issue561-5-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:30:56.683529400 +0200
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
