--- before_pass
+++ after_pass
@@ -24,7 +24,6 @@ control c(out B32 x) {
     apply {
         k = 32w0;
         x = 32w0;
-        ;
         t.apply();
         x = 32w3;
     }
