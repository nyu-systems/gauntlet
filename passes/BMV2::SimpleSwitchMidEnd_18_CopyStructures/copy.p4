--- before_pass
+++ after_pass
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
