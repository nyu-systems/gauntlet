--- before_pass
+++ after_pass
@@ -10,10 +10,6 @@ header H {
 }
 control c(out B32 x) {
     N32 k_0;
-    bit<32> b_0;
-    N32 n_0;
-    N32 n1_0;
-    S s_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("c.t") table t_0 {
@@ -26,17 +22,12 @@ control c(out B32 x) {
         default_action = NoAction_0();
     }
     apply {
-        b_0 = 32w0;
-        n_0 = b_0;
-        k_0 = n_0;
-        x = (B32)n_0;
-        n1_0 = 32w1;
-        if (n_0 == n1_0) 
+        k_0 = 32w0;
+        x = (B32)32w0;
+        if (32w0 == 32w1) 
             x = 32w2;
-        s_0.b = b_0;
-        s_0.n = n_0;
         t_0.apply();
-        if (s_0.b == (B32)s_0.n) 
+        if (32w0 == (B32)32w0) 
             x = 32w3;
     }
 }
