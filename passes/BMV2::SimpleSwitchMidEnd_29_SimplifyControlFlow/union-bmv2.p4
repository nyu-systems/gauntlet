--- dumps/p4_16_samples/union-bmv2.p4/pruned/union-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:32:34.467813000 +0200
+++ dumps/p4_16_samples/union-bmv2.p4/pruned/union-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:32:34.470209600 +0200
@@ -48,10 +48,8 @@ control egress(inout Headers h, inout Me
 control deparser(packet_out b, in Headers h) {
     apply {
         b.emit<Hdr1>(h.h1);
-        {
-            b.emit<Hdr1>(h.u.h1);
-            b.emit<Hdr2>(h.u.h2);
-        }
+        b.emit<Hdr1>(h.u.h1);
+        b.emit<Hdr2>(h.u.h2);
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
