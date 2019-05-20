--- dumps/p4_16_samples/issue561-6-bmv2.p4/pruned/issue561-6-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:30:57.464700500 +0200
+++ dumps/p4_16_samples/issue561-6-bmv2.p4/pruned/issue561-6-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:30:57.519407200 +0200
@@ -85,11 +85,9 @@ control egress(inout headers hdr, inout
 }
 control DeparserImpl(packet_out packet, in headers hdr) {
     apply {
-        {
-            packet.emit<S>(hdr.base);
-            packet.emit<U>(hdr.u[0]);
-            packet.emit<U>(hdr.u[1]);
-        }
+        packet.emit<S>(hdr.base);
+        packet.emit<U>(hdr.u[0]);
+        packet.emit<U>(hdr.u[1]);
     }
 }
 control verifyChecksum(inout headers hdr, inout metadata meta) {
