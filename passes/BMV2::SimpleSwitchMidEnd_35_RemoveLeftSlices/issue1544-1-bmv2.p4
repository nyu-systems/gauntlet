--- before_pass
+++ after_pass
@@ -85,7 +85,7 @@ control ingress(inout headers hdr, inout
             tmp_0 = hdr.ethernet.srcAddr[15:0] + 16w65535;
         else 
             tmp_0 = hdr.ethernet.srcAddr[15:0];
-        hdr.ethernet.srcAddr[15:0] = tmp_0;
+        hdr.ethernet.srcAddr = hdr.ethernet.srcAddr & ~48w0xffff | (bit<48>)tmp_0 << 0 & 48w0xffff;
     }
 }
 control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
