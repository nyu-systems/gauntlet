--- dumps/pruned/virtual-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:34:26.846221500 +0200
+++ dumps/pruned/virtual-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:34:26.852069100 +0200
@@ -15,7 +15,10 @@ control c(inout bit<16> p) {
         }
         void g(inout data x) {
             data ix_1;
-            ix_1 = x;
+            {
+                ix_1.a = x.a;
+                ix_1.b = x.b;
+            }
             if (ix_1.a < ix_1.b) 
                 x.a = ix_1.a + 16w1;
             if (ix_1.a > ix_1.b) 
