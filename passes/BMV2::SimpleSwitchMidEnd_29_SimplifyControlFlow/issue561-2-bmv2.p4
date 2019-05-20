--- dumps/p4_16_samples/issue561-2-bmv2.p4/pruned/issue561-2-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:30:55.172450200 +0200
+++ dumps/p4_16_samples/issue561-2-bmv2.p4/pruned/issue561-2-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:30:55.227647200 +0200
@@ -69,11 +69,9 @@ control egress(inout headers hdr, inout
 }
 control DeparserImpl(packet_out packet, in headers hdr) {
     apply {
-        {
-            packet.emit<S>(hdr.base);
-            packet.emit<O1>(hdr.u.byte);
-            packet.emit<O2>(hdr.u.short);
-        }
+        packet.emit<S>(hdr.base);
+        packet.emit<O1>(hdr.u.byte);
+        packet.emit<O2>(hdr.u.short);
     }
 }
 control verifyChecksum(inout headers hdr, inout metadata meta) {
