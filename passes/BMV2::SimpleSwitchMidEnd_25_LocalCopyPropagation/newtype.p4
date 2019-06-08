--- before_pass
+++ after_pass
@@ -10,10 +10,6 @@ header H {
 }
 control c(out B32 x) {
     N32 k;
-    bit<32> b_1;
-    N32 n_1;
-    N32 n1;
-    S s;
     @name(".NoAction") action NoAction_0() {
     }
     @name("c.t") table t {
@@ -26,17 +22,12 @@ control c(out B32 x) {
         default_action = NoAction_0();
     }
     apply {
-        b_1 = 32w0;
-        n_1 = b_1;
-        k = n_1;
-        x = (B32)n_1;
-        n1 = 32w1;
-        if (n_1 == n1) 
+        k = 32w0;
+        x = (B32)32w0;
+        if (32w0 == 32w1) 
             x = 32w2;
-        s.b = b_1;
-        s.n = n_1;
         t.apply();
-        if (s.b == (B32)s.n) 
+        if (32w0 == (B32)32w0) 
             x = 32w3;
     }
 }
