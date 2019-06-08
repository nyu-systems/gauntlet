--- before_pass
+++ after_pass
@@ -4,7 +4,7 @@ typedef bit<32> Wide_t;
 typedef Wide_t Wide;
 control c(out bool b) {
     apply {
-        b = (Narrow_t)(Wide_t)32w3 == 9w10;
+        b = false;
     }
 }
 control ctrl(out bool b);
