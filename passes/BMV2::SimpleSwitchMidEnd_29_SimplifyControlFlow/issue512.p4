--- dumps/p4_16_samples/issue512.p4/pruned/issue512-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:30:53.701209700 +0200
+++ dumps/p4_16_samples/issue512.p4/pruned/issue512-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:30:53.765753200 +0200
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
