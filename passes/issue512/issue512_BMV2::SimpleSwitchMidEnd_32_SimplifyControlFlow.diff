--- before_pass
+++ after_pass
@@ -28,19 +28,9 @@ control cIngress(inout Parsed_packet hdr
     bool pred;
     @name("cIngress.foo") action foo() {
         meta.b = meta.b + 4w5;
-        {
-            {
-                pred = meta.b > 4w10;
-                {
-                    meta.b = (meta.b > 4w10 ? meta.b ^ 4w5 : meta.b);
-                }
-            }
-        }
-        {
-            {
-                meta.b = (!(pred ? true : false) ? meta.b + 4w5 : meta.b);
-            }
-        }
+        pred = meta.b > 4w10;
+        meta.b = (meta.b > 4w10 ? meta.b ^ 4w5 : meta.b);
+        meta.b = (!(pred ? true : false) ? meta.b + 4w5 : meta.b);
     }
     @name("cIngress.guh") table guh_0 {
         key = {
