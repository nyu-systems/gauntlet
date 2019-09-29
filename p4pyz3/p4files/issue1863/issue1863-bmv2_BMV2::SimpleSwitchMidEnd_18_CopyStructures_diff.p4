--- before_pass
+++ after_pass
@@ -35,8 +35,14 @@ control ingressImpl(inout headers_t hdr,
     foo_t foo_0;
     apply {
         stdmeta.egress_spec = 9w0;
-        foo_0 = { 8w1, 8w2 };
-        foo_0 = {foo_0.b,foo_0.a};
+        {
+            foo_0.a = 8w1;
+            foo_0.b = 8w2;
+        }
+        {
+            foo_0.a = foo_0.b;
+            foo_0.b = foo_0.a;
+        }
         hdr.custom.a = foo_0.a;
         hdr.custom.b = foo_0.b;
     }
