--- dumps/pruned/pvs-struct-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:33:29.429425800 +0200
+++ dumps/pruned/pvs-struct-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:33:29.434246900 +0200
@@ -31,7 +31,6 @@ control MyVerifyChecksum(inout my_packet
     }
 }
 control MyIngress(inout my_packet p, inout my_metadata meta, inout standard_metadata_t s) {
-    bit<32> key_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("MyIngress.set_data") action set_data_0() {
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
             t.apply();
         }
     }
