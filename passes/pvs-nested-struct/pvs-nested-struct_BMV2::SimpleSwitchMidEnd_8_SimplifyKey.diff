--- before_pass
+++ after_pass
@@ -39,18 +39,22 @@ control MyIngress(inout my_packet p, ino
     }
     @name("MyIngress.set_data") action set_data() {
     }
+    bit<32> key_0;
     @name("MyIngress.t") table t_0 {
         actions = {
             set_data();
             @defaultonly NoAction_0();
         }
         key = {
-            meta.data[0].da: exact @name("meta.data[0].da") ;
+            key_0: exact @name("meta.data[0].da") ;
         }
         default_action = NoAction_0();
     }
     apply {
-        t_0.apply();
+        {
+            key_0 = meta.data[0].da;
+            t_0.apply();
+        }
     }
 }
 control MyEgress(inout my_packet p, inout my_metadata m, inout standard_metadata_t s) {
