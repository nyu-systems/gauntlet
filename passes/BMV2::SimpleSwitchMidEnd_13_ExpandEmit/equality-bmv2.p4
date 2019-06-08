--- dumps/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-06-08 18:31:34.646301600 +0200
+++ dumps/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:31:34.647974900 +0200
@@ -54,7 +54,12 @@ control uc(inout headers hdr, inout meta
 }
 control deparser(packet_out packet, in headers hdr) {
     apply {
-        packet.emit<headers>(hdr);
+        {
+            packet.emit<H>(hdr.h);
+            packet.emit<H>(hdr.a[0]);
+            packet.emit<H>(hdr.a[1]);
+            packet.emit<Same>(hdr.same);
+        }
     }
 }
 V1Switch<headers, metadata>(p(), vc(), ingress(), egress(), uc(), deparser()) main;
