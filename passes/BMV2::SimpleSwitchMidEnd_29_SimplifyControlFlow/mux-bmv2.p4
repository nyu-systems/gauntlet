--- dumps/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:58.178972500 +0200
+++ dumps/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:58.249082300 +0200
@@ -19,12 +19,8 @@ control Eg(inout Headers hdrs, inout Met
     bit<64> val;
     @name("Eg.update") action update_0() {
         val = res;
-        {
-            {
-                tmp_0 = res[31:0];
-                tmp_0 = tmp_0;
-            }
-        }
+        tmp_0 = res[31:0];
+        tmp_0 = tmp_0;
         val[31:0] = tmp_0;
         res = val;
     }
