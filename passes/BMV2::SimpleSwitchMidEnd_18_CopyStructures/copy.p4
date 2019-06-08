--- dumps/pruned/copy-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:31:28.676484000 +0200
+++ dumps/pruned/copy-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:31:28.679110600 +0200
@@ -5,9 +5,15 @@ control c(inout bit<32> b) {
     S s1;
     S s2;
     @name("c.a") action a_0() {
-        s2 = { 32w0 };
-        s1 = s2;
-        s2 = s1;
+        {
+            s2.x = 32w0;
+        }
+        {
+            s1.x = s2.x;
+        }
+        {
+            s2.x = s1.x;
+        }
         b = s2.x;
     }
     apply {
