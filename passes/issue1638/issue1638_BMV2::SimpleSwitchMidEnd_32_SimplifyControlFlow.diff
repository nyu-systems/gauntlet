--- before_pass
+++ after_pass
@@ -28,10 +28,8 @@ control MyC(inout hdr_t hdr, inout meta_
         default_action = NoAction_0();
     }
     apply {
-        {
-            key_0 = 8w0;
-            c2_a.apply();
-        }
+        key_0 = 8w0;
+        c2_a.apply();
     }
 }
 P<hdr_t, meta_t>(MyC()) main;
