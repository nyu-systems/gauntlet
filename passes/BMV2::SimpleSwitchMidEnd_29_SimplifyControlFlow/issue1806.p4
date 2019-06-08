--- dumps/pruned/issue1806-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:14.102748000 +0200
+++ dumps/pruned/issue1806-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:14.105218700 +0200
@@ -29,9 +29,7 @@ control c(inout Headers h, inout standar
         default_action = NoAction_0();
     }
     apply {
-        {
-            tns.apply();
-        }
+        tns.apply();
     }
 }
 parser p<H>(packet_in _p, out H h);
