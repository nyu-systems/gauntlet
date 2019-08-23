--- before_pass
+++ after_pass
@@ -31,7 +31,6 @@ control MyVerifyChecksum(inout my_packet
     }
 }
 control MyIngress(inout my_packet p, inout my_metadata meta, inout standard_metadata_t s) {
-    bit<32> key_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("MyIngress.set_data") action set_data() {
@@ -42,13 +41,12 @@ control MyIngress(inout my_packet p, ino
             @defaultonly NoAction_0();
         }
         key = {
-            key_0: exact @name("meta.data[0].da") ;
+            meta.data[0].da: exact @name("meta.data[0].da") ;
         }
         default_action = NoAction_0();
     }
     apply {
         {
-            key_0 = meta.data[0].da;
             t_0.apply();
         }
     }
