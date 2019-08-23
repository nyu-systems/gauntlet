--- before_pass
+++ after_pass
@@ -13,19 +13,18 @@ package top(ct _ct);
 control c(out bit<32> x) {
     U u_0;
     U[2] u2_0;
-    bool b_0;
     apply {
-        b_0 = u_0.isValid();
+        u_0.isValid();
         u_0.h1.isValid();
         x = u_0.h1.f + u_0.h2.g;
         u_0.h1.setValid();
         u_0.h1.f = 32w0;
-        x = x + u_0.h1.f;
+        x = x + 32w0;
         u_0.h2.g = 32w0;
-        x = x + u_0.h2.g;
+        x = x + 32w0;
         u2_0[0].h1.setValid();
         u2_0[0].h1.f = 32w2;
-        x = x + u2_0[1].h2.g + u2_0[0].h1.f;
+        x = x + u2_0[1].h2.g + 32w2;
     }
 }
 top(c()) main;
