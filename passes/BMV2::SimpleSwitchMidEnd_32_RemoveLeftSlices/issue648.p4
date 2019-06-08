--- dumps/pruned/issue648-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-06-08 18:32:38.106748100 +0200
+++ dumps/pruned/issue648-BMV2::SimpleSwitchMidEnd_32_RemoveLeftSlices.p4	2019-06-08 18:32:38.108746200 +0200
@@ -6,8 +6,8 @@ header hdr {
 }
 control ingress(inout hdr h) {
     apply {
-        h.a[7:0] = ((bit<32>)h.c)[7:0];
-        h.a[15:8] = (h.c + h.c)[7:0];
+        h.a = h.a & ~32w0xff | (bit<32>)((bit<32>)h.c)[7:0] << 0 & 32w0xff;
+        h.a = h.a & ~32w0xff00 | (bit<32>)(h.c + h.c)[7:0] << 8 & 32w0xff00;
     }
 }
 control c(inout hdr h);
