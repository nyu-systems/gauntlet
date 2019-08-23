--- before_pass
+++ after_pass
@@ -22,7 +22,6 @@ control verifyChecksum(inout headers_t h
     }
 }
 control ingressImpl(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
-    bit<5> key_0;
     bit<16> key_1;
     @name(".NoAction") action NoAction_0() {
     }
@@ -35,7 +34,7 @@ control ingressImpl(inout headers_t hdr,
     }
     @name("ingressImpl.t1") table t1_0 {
         key = {
-            key_0                                  : exact @name("ethernet.srcAddr.slice") ;
+            hdr.ethernet.srcAddr[22:18]            : exact @name("ethernet.srcAddr.slice") ;
             hdr.ethernet.dstAddr & 48w0x10101010101: exact @name("dstAddr_lsbs") ;
             key_1                                  : exact @name("etherType_less_10") ;
         }
@@ -48,7 +47,6 @@ control ingressImpl(inout headers_t hdr,
     }
     apply {
         {
-            key_0 = hdr.ethernet.srcAddr[22:18];
             key_1 = hdr.ethernet.etherType + 16w65526;
             t1_0.apply();
         }
