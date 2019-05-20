--- dumps/p4_16_samples/virtual.p4/pruned/virtual-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:32:41.919085700 +0200
+++ dumps/p4_16_samples/virtual.p4/pruned/virtual-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:32:42.047131600 +0200
@@ -15,10 +15,8 @@ control c(inout bit<16> p) {
         }
         void g(inout data x) {
             data ix_1;
-            {
-                ix_1.a = x.a;
-                ix_1.b = x.b;
-            }
+            ix_1.a = x.a;
+            ix_1.b = x.b;
             if (x.a < x.b) 
                 x.a = x.a + 16w1;
             if (ix_1.a > x.b) 
