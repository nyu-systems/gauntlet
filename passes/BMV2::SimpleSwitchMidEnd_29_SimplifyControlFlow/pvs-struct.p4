--- dumps/p4_16_samples/pvs-struct.p4/pruned/pvs-struct-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:31:55.782640800 +0200
+++ dumps/p4_16_samples/pvs-struct.p4/pruned/pvs-struct-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:31:55.790306100 +0200
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
