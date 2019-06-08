--- dumps/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:31:34.674239900 +0200
+++ dumps/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:31:34.706004300 +0200
@@ -54,12 +54,10 @@ control uc(inout headers hdr, inout meta
 }
 control deparser(packet_out packet, in headers hdr) {
     apply {
-        {
-            packet.emit<H>(hdr.h);
-            packet.emit<H>(hdr.a[0]);
-            packet.emit<H>(hdr.a[1]);
-            packet.emit<Same>(hdr.same);
-        }
+        packet.emit<H>(hdr.h);
+        packet.emit<H>(hdr.a[0]);
+        packet.emit<H>(hdr.a[1]);
+        packet.emit<Same>(hdr.same);
     }
 }
 V1Switch<headers, metadata>(p(), vc(), ingress(), egress(), uc(), deparser()) main;
