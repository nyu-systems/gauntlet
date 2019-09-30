--- before_pass
+++ after_pass
@@ -32,19 +32,10 @@ control verifyChecksum(inout headers_t h
     }
 }
 control ingressImpl(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
-    foo_t foo_0;
     apply {
         stdmeta.egress_spec = 9w0;
-        {
-            foo_0.a = 8w1;
-            foo_0.b = 8w2;
-        }
-        {
-            foo_0.a = foo_0.b;
-            foo_0.b = foo_0.a;
-        }
-        hdr.custom.a = foo_0.a;
-        hdr.custom.b = foo_0.b;
+        hdr.custom.a = 8w2;
+        hdr.custom.b = 8w2;
     }
 }
 control egressImpl(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
