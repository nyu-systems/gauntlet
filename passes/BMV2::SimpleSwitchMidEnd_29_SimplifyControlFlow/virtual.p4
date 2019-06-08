--- dumps/pruned/virtual-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:34:26.895750800 +0200
+++ dumps/pruned/virtual-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:34:26.962044900 +0200
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
