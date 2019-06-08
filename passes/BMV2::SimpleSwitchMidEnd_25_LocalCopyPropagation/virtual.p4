--- dumps/pruned/virtual-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:34:26.879820000 +0200
+++ dumps/pruned/virtual-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:34:26.883957700 +0200
@@ -19,9 +19,9 @@ control c(inout bit<16> p) {
                 ix_1.a = x.a;
                 ix_1.b = x.b;
             }
-            if (ix_1.a < ix_1.b) 
-                x.a = ix_1.a + 16w1;
-            if (ix_1.a > ix_1.b) 
+            if (x.a < x.b) 
+                x.a = x.a + 16w1;
+            if (ix_1.a > x.b) 
                 x.a = ix_1.a + 16w65535;
         }
     };
