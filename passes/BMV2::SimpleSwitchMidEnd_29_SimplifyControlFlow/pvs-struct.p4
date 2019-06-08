--- before_pass
+++ after_pass
@@ -46,9 +46,7 @@ control MyIngress(inout my_packet p, ino
         default_action = NoAction_0();
     }
     apply {
-        {
-            t.apply();
-        }
+        t.apply();
     }
 }
 control MyEgress(inout my_packet p, inout my_metadata m, inout standard_metadata_t s) {
