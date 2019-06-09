--- before_pass
+++ after_pass
@@ -23,6 +23,7 @@ control verifyChecksum(inout headers_t h
 }
 control ingressImpl(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
     bit<16> key_1;
+    bit<5> key_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("ingressImpl.my_drop") action my_drop() {
@@ -32,7 +33,6 @@ control ingressImpl(inout headers_t hdr,
         hdr.ethernet.dstAddr[22:18] = hdr.ethernet.srcAddr[5:1];
         stdmeta.egress_spec = out_port;
     }
-    bit<5> key_0;
     @name("ingressImpl.t1") table t1_0 {
         key = {
             key_0                                  : exact @name("ethernet.srcAddr.slice") ;
