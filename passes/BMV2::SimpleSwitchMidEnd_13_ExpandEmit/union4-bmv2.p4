--- dumps/pruned/union4-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-06-08 18:34:22.557400400 +0200
+++ dumps/pruned/union4-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:34:22.559120100 +0200
@@ -49,7 +49,10 @@ control egress(inout Headers h, inout Me
 control deparser(packet_out b, in Headers h) {
     apply {
         b.emit<Hdr1>(h.h1);
-        b.emit<U>(h.u);
+        {
+            b.emit<Hdr1>(h.u.h1);
+            b.emit<Hdr2>(h.u.h2);
+        }
         b.emit<Hdr2>(h.h2);
     }
 }
