--- dumps/pruned/issue561-1-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:33.426370400 +0200
+++ dumps/pruned/issue561-1-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:33.462466600 +0200
@@ -66,11 +66,9 @@ control egress(inout headers hdr, inout
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
