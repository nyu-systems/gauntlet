--- before_pass
+++ after_pass
@@ -3,12 +3,8 @@ typedef Narrow_t Narrow;
 typedef bit<32> Wide_t;
 typedef Wide_t Wide;
 control c(out bool b) {
-    Wide x_0;
-    Narrow y_0;
     apply {
-        x_0 = 32w3;
-        y_0 = (Narrow_t)(Wide_t)x_0;
-        b = y_0 == 9w10;
+        b = (Narrow_t)(Wide_t)32w3 == 9w10;
     }
 }
 control ctrl(out bool b);
