--- before_pass
+++ after_pass
@@ -2,14 +2,8 @@
 parser simple(out bit<2> z);
 package m(simple n);
 parser p2_0(out bit<2> z2) {
-    bit<2> x1_0;
-    bit<2> x2_0;
-    bit<2> x3_0;
     state start {
-        x1_0 = 2w0;
-        x2_0 = 2w1;
-        x3_0 = 2w2;
-        z2 = 2w3 | x1_0 | x2_0 | x3_0;
+        z2 = 2w3 | 2w0 | 2w1 | 2w2;
         transition accept;
     }
 }
