--- dumps/p4_16_samples/issue774-4-bmv2.p4/pruned/issue774-4-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:31:04.558659500 +0200
+++ dumps/p4_16_samples/issue774-4-bmv2.p4/pruned/issue774-4-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:31:04.624636300 +0200
@@ -34,9 +34,7 @@ control cc(inout Headers hdr, inout M me
 }
 control d(packet_out b, in Headers hdr) {
     apply {
-        {
-            b.emit<Header>(hdr.h);
-        }
+        b.emit<Header>(hdr.h);
     }
 }
 V1Switch<Headers, M>(prs(), vc(), i(), e(), cc(), d()) main;
