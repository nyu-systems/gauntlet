--- dumps/p4_16_samples/issue1806.p4/pruned/issue1806-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:30:30.725380800 +0200
+++ dumps/p4_16_samples/issue1806.p4/pruned/issue1806-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:30:30.728546600 +0200
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
