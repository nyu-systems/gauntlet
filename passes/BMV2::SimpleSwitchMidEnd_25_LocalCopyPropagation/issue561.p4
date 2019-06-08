--- before_pass
+++ after_pass
@@ -13,19 +13,18 @@ package top(ct _ct);
 control c(out bit<32> x) {
     U u;
     U[2] u2;
-    bool b_1;
     apply {
-        b_1 = u.isValid();
+        u.isValid();
         u.h1.isValid();
         x = u.h1.f + u.h2.g;
         u.h1.setValid();
         u.h1.f = 32w0;
-        x = x + u.h1.f;
+        x = x + 32w0;
         u.h2.g = 32w0;
-        x = x + u.h2.g;
+        x = x + 32w0;
         u2[0].h1.setValid();
         u2[0].h1.f = 32w2;
-        x = x + u2[1].h2.g + u2[0].h1.f;
+        x = x + u2[1].h2.g + 32w2;
     }
 }
 top(c()) main;
