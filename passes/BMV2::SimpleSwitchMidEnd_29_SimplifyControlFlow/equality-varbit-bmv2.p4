--- dumps/pruned/equality-varbit-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:31:34.988793200 +0200
+++ dumps/pruned/equality-varbit-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:31:34.990810400 +0200
@@ -38,9 +38,7 @@ control uc(inout headers hdr, inout meta
 }
 control deparser(packet_out packet, in headers hdr) {
     apply {
-        {
-            packet.emit<H>(hdr.h);
-        }
+        packet.emit<H>(hdr.h);
     }
 }
 V1Switch<headers, metadata>(p(), vc(), ingress(), egress(), uc(), deparser()) main;
