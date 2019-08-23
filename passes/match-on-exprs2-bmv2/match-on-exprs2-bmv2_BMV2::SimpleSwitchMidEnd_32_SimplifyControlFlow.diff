--- before_pass
+++ after_pass
@@ -47,13 +47,9 @@ control ingressImpl(inout headers_t hdr,
         const default_action = NoAction_0();
     }
     apply {
-        {
-            key_1 = hdr.ethernet.etherType + 16w65526;
-            {
-                key_0 = hdr.ethernet.srcAddr[22:18];
-                t1_0.apply();
-            }
-        }
+        key_1 = hdr.ethernet.etherType + 16w65526;
+        key_0 = hdr.ethernet.srcAddr[22:18];
+        t1_0.apply();
     }
 }
 control egressImpl(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
