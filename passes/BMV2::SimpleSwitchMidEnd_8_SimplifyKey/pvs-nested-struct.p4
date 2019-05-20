--- dumps/p4_16_samples/pvs-nested-struct.p4/pruned/pvs-nested-struct-BMV2::SimpleSwitchMidEnd_7_TypeChecking.p4	2019-05-20 17:32:23.387650300 +0200
+++ dumps/p4_16_samples/pvs-nested-struct.p4/pruned/pvs-nested-struct-BMV2::SimpleSwitchMidEnd_8_SimplifyKey.p4	2019-05-20 17:32:23.392427300 +0200
@@ -39,18 +39,22 @@ control MyIngress(inout my_packet p, ino
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
