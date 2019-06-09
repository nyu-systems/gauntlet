--- before_pass
+++ after_pass
@@ -52,7 +52,7 @@ control ingressImpl(inout headers_t hdr,
                                     error_as_int_0 = 8w6;
                                 else 
                                     error_as_int_0 = 8w7;
-        hdr.ethernet.dstAddr[7:0] = error_as_int_0;
+        hdr.ethernet.dstAddr = hdr.ethernet.dstAddr & ~48w0xff | (bit<48>)error_as_int_0 << 0 & 48w0xff;
     }
 }
 control egressImpl(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
