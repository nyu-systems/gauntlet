--- before_pass
+++ after_pass
@@ -51,12 +51,8 @@ control MyIngress(inout my_packet p, ino
         default_action = NoAction_0();
     }
     apply {
-        {
-            {
-                key_0 = meta.data[0].da;
-                t_0.apply();
-            }
-        }
+        key_0 = meta.data[0].da;
+        t_0.apply();
     }
 }
 control MyEgress(inout my_packet p, inout my_metadata m, inout standard_metadata_t s) {
