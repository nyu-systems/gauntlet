--- dumps/pruned/pvs-nested-struct-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:34:11.357586200 +0200
+++ dumps/pruned/pvs-nested-struct-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:34:11.359893500 +0200
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
