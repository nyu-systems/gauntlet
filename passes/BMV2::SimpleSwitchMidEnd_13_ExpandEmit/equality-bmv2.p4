--- dumps/p4_16_samples/equality-bmv2.p4/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:29:40.172884900 +0200
+++ dumps/p4_16_samples/equality-bmv2.p4/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:29:40.177256900 +0200
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
