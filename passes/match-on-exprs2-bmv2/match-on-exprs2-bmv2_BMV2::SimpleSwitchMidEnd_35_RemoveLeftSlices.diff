--- before_pass
+++ after_pass
@@ -30,7 +30,7 @@ control ingressImpl(inout headers_t hdr,
         mark_to_drop(stdmeta);
     }
     @name("ingressImpl.foo") action foo(bit<9> out_port) {
-        hdr.ethernet.dstAddr[22:18] = hdr.ethernet.srcAddr[5:1];
+        hdr.ethernet.dstAddr = hdr.ethernet.dstAddr & ~48w0x7c0000 | (bit<48>)hdr.ethernet.srcAddr[5:1] << 18 & 48w0x7c0000;
         stdmeta.egress_spec = out_port;
     }
     @name("ingressImpl.t1") table t1_0 {
