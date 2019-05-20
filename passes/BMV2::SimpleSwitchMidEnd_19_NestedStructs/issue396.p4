--- dumps/p4_16_samples/issue396.p4/pruned/issue396-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:30:45.739721100 +0200
+++ dumps/p4_16_samples/issue396.p4/pruned/issue396-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-05-20 17:30:45.846035600 +0200
@@ -9,8 +9,8 @@ package top(c _c);
 control d(out bool b) {
     H h_1;
     H[2] h3;
-    S s;
-    S s1;
+    H s_h;
+    H s1_h;
     bool eout;
     H tmp_0;
     apply {
@@ -18,10 +18,10 @@ control d(out bool b) {
         {
             h_1.x = 32w0;
         }
-        s.h.setValid();
-        s1.h.setValid();
+        s_h.setValid();
+        s1_h.setValid();
         {
-            s1.h.x = 32w0;
+            s1_h.x = 32w0;
         }
         h3[0].setValid();
         h3[1].setValid();
@@ -33,7 +33,7 @@ control d(out bool b) {
             tmp_0.x = 32w0;
         }
         eout = tmp_0.isValid();
-        b = h_1.isValid() && eout && h3[1].isValid() && s1.h.isValid();
+        b = h_1.isValid() && eout && h3[1].isValid() && s1_h.isValid();
     }
 }
 top(d()) main;
