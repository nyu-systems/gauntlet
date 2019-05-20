--- dumps/p4_16_samples/mux-bmv2.p4/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:31:24.657156000 +0200
+++ dumps/p4_16_samples/mux-bmv2.p4/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:31:24.719344500 +0200
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
