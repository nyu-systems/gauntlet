--- before_pass
+++ after_pass
@@ -83,8 +83,8 @@ control ingress(inout headers hdr, inout
     }
     apply {
         mac_da_0.apply();
-        hdr.ethernet.srcAddr[15:0] = hdr.ethernet.srcAddr[15:0] + (hdr.ethernet.srcAddr[15:0] + 16w1);
-        hdr.ethernet.srcAddr[15:0] = hdr.ethernet.srcAddr[15:0] + 16w1;
+        hdr.ethernet.srcAddr = hdr.ethernet.srcAddr & ~48w0xffff | (bit<48>)(hdr.ethernet.srcAddr[15:0] + (hdr.ethernet.srcAddr[15:0] + 16w1)) << 0 & 48w0xffff;
+        hdr.ethernet.srcAddr = hdr.ethernet.srcAddr & ~48w0xffff | (bit<48>)(hdr.ethernet.srcAddr[15:0] + 16w1) << 0 & 48w0xffff;
         hdr.ethernet.etherType = hdr.ethernet.etherType + 16w1;
     }
 }
