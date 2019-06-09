--- before_pass
+++ after_pass
@@ -2,10 +2,7 @@ struct S {
     bit<32> f;
 }
 control caller() {
-    S data_0;
     apply {
-        data_0.f = 32w0;
-        data_0.f = 32w0;
     }
 }
 control none();
