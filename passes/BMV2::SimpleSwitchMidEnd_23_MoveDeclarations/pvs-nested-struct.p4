--- dumps/pruned/pvs-nested-struct-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-06-08 18:34:11.338219600 +0200
+++ dumps/pruned/pvs-nested-struct-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-06-08 18:34:11.344000600 +0200
@@ -35,11 +35,11 @@ control MyVerifyChecksum(inout my_packet
     }
 }
 control MyIngress(inout my_packet p, inout my_metadata meta, inout standard_metadata_t s) {
+    bit<32> key_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("MyIngress.set_data") action set_data_0() {
     }
-    bit<32> key_0;
     @name("MyIngress.t") table t {
         actions = {
             set_data_0();
