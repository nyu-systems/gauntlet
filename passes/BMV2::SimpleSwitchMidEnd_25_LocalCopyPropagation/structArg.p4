--- before_pass
+++ after_pass
@@ -2,10 +2,7 @@ struct S {
     bit<32> f;
 }
 control caller() {
-    S data;
     apply {
-        data.f = 32w0;
-        data.f = 32w0;
     }
 }
 control none();
