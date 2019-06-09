--- before_pass
+++ after_pass
@@ -2,10 +2,8 @@
 header h {
 }
 control c(out bit<32> x) {
-    bit<32> sz_0;
     apply {
-        sz_0 = 32w4;
-        x = sz_0;
+        x = 32w4;
     }
 }
 control Simpler(out bit<32> x);
