--- dumps/p4_16_samples/issue561-7-bmv2.p4/pruned/issue561-7-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:31:12.260413000 +0200
+++ dumps/p4_16_samples/issue561-7-bmv2.p4/pruned/issue561-7-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:31:12.316142100 +0200
@@ -66,10 +66,8 @@ control egress(inout headers hdr, inout
 }
 control DeparserImpl(packet_out packet, in headers hdr) {
     apply {
-        {
-            packet.emit<S>(hdr.base);
-            packet.emit<U>(hdr.u[0]);
-        }
+        packet.emit<S>(hdr.base);
+        packet.emit<U>(hdr.u[0]);
     }
 }
 control verifyChecksum(inout headers hdr, inout metadata meta) {
