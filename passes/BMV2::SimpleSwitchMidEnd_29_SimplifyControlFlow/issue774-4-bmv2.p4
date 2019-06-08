--- dumps/pruned/issue774-4-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:40.940557100 +0200
+++ dumps/pruned/issue774-4-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:40.973670100 +0200
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
