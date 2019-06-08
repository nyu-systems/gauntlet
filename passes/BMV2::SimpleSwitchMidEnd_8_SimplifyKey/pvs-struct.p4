--- before_pass
+++ after_pass
@@ -35,18 +35,22 @@ control MyIngress(inout my_packet p, ino
     }
     @name("MyIngress.set_data") action set_data_0() {
     }
+    bit<32> key_0;
     @name("MyIngress.t") table t {
         actions = {
             set_data_0();
             @defaultonly NoAction_0();
         }
         key = {
-            meta.data[0].da: exact @name("meta.data[0].da") ;
+            key_0: exact @name("meta.data[0].da") ;
         }
         default_action = NoAction_0();
     }
     apply {
-        t.apply();
+        {
+            key_0 = meta.data[0].da;
+            t.apply();
+        }
     }
 }
 control MyEgress(inout my_packet p, inout my_metadata m, inout standard_metadata_t s) {
