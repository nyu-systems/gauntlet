--- before_pass
+++ after_pass
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
