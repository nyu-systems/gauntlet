--- dumps/p4_16_samples/pvs-nested-struct.p4/pruned/pvs-nested-struct-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:32:23.349708800 +0200
+++ dumps/p4_16_samples/pvs-nested-struct.p4/pruned/pvs-nested-struct-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:32:23.351762500 +0200
@@ -50,9 +50,7 @@ control MyIngress(inout my_packet p, ino
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
