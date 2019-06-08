--- dumps/pruned/issue512-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:32.786286500 +0200
+++ dumps/pruned/issue512-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:32.832131200 +0200
@@ -28,19 +28,9 @@ control cIngress(inout Parsed_packet hdr
     bool pred;
     @name("cIngress.foo") action foo_0() {
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
     @name("cIngress.guh") table guh {
         key = {
