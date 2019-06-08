--- dumps/pruned/pvs-struct-BMV2::SimpleSwitchMidEnd_7_TypeChecking.p4	2019-06-08 18:33:29.519419800 +0200
+++ dumps/pruned/pvs-struct-BMV2::SimpleSwitchMidEnd_8_SimplifyKey.p4	2019-06-08 18:33:29.523845100 +0200
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
