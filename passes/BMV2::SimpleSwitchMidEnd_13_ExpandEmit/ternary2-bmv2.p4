--- dumps/pruned/ternary2-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-06-08 18:34:16.755586900 +0200
+++ dumps/pruned/ternary2-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:34:16.758090900 +0200
@@ -162,7 +162,12 @@ control egress(inout packet_t hdrs, inou
 control deparser(packet_out b, in packet_t hdrs) {
     apply {
         b.emit<data_h>(hdrs.data);
-        b.emit<extra_h[4]>(hdrs.extra);
+        {
+            b.emit<extra_h>(hdrs.extra[0]);
+            b.emit<extra_h>(hdrs.extra[1]);
+            b.emit<extra_h>(hdrs.extra[2]);
+            b.emit<extra_h>(hdrs.extra[3]);
+        }
     }
 }
 V1Switch<packet_t, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
