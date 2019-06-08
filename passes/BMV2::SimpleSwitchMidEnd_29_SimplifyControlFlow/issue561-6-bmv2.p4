--- dumps/pruned/issue561-6-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:36.341466300 +0200
+++ dumps/pruned/issue561-6-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:36.389358600 +0200
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
