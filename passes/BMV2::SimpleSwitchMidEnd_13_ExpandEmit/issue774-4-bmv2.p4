--- dumps/pruned/issue774-4-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-06-08 18:32:40.906576400 +0200
+++ dumps/pruned/issue774-4-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:32:40.910017700 +0200
@@ -34,7 +34,9 @@ control cc(inout Headers hdr, inout M me
 }
 control d(packet_out b, in Headers hdr) {
     apply {
-        b.emit<Headers>(hdr);
+        {
+            b.emit<Header>(hdr.h);
+        }
     }
 }
 V1Switch<Headers, M>(prs(), vc(), i(), e(), cc(), d()) main;
