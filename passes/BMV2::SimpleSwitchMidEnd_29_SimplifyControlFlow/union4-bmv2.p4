--- dumps/p4_16_samples/union4-bmv2.p4/pruned/union4-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:32:37.386966600 +0200
+++ dumps/p4_16_samples/union4-bmv2.p4/pruned/union4-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:32:37.389180000 +0200
@@ -49,10 +49,8 @@ control egress(inout Headers h, inout Me
 control deparser(packet_out b, in Headers h) {
     apply {
         b.emit<Hdr1>(h.h1);
-        {
-            b.emit<Hdr1>(h.u.h1);
-            b.emit<Hdr2>(h.u.h2);
-        }
+        b.emit<Hdr1>(h.u.h1);
+        b.emit<Hdr2>(h.u.h2);
         b.emit<Hdr2>(h.h2);
     }
 }
