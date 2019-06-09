--- before_pass
+++ after_pass
@@ -85,7 +85,7 @@ control ingress(inout headers hdr, inout
             retval = hdr.ethernet.srcAddr[15:0] + 16w65535;
         else 
             retval = hdr.ethernet.srcAddr[15:0];
-        hdr.ethernet.srcAddr[15:0] = retval;
+        hdr.ethernet.srcAddr = hdr.ethernet.srcAddr & ~48w0xffff | (bit<48>)retval << 0 & 48w0xffff;
     }
 }
 control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
