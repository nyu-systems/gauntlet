--- dumps/pruned/pvs-struct-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:33:29.450863600 +0200
+++ dumps/pruned/pvs-struct-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:33:29.455197000 +0200
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
