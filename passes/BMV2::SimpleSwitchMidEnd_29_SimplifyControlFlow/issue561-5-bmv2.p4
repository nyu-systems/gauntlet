--- dumps/p4_16_samples/issue561-5-bmv2.p4/pruned/issue561-5-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:30:56.733727400 +0200
+++ dumps/p4_16_samples/issue561-5-bmv2.p4/pruned/issue561-5-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:30:56.829465800 +0200
@@ -65,10 +65,8 @@ control egress(inout headers hdr, inout
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
