--- before_pass
+++ after_pass
@@ -1,6 +1,6 @@
 #include <core.p4>
 typedef bit<32> B32;
-type bit<32> N32;
+typedef bit<32> N32;
 struct S {
     B32 b;
     N32 n;
@@ -27,10 +27,10 @@ control c(out B32 x) {
     }
     apply {
         b_1 = 32w0;
-        n_1 = (N32)b_1;
+        n_1 = b_1;
         k = n_1;
         x = (B32)n_1;
-        n1 = (N32)32w1;
+        n1 = 32w1;
         if (n_1 == n1) 
             x = 32w2;
         s.b = b_1;
