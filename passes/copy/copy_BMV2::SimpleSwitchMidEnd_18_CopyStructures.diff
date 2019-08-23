--- before_pass
+++ after_pass
@@ -5,9 +5,15 @@ control c(inout bit<32> b) {
     S s1_0;
     S s2_0;
     @name("c.a") action a() {
-        s2_0 = S {x = 32w0};
-        s1_0 = s2_0;
-        s2_0 = s1_0;
+        {
+            s2_0.x = 32w0;
+        }
+        {
+            s1_0.x = s2_0.x;
+        }
+        {
+            s2_0.x = s1_0.x;
+        }
         b = s2_0.x;
     }
     apply {
