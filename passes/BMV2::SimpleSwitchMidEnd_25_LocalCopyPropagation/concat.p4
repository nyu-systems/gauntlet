--- before_pass
+++ after_pass
@@ -1,12 +1,8 @@
 control proto(out bit<32> x);
 package top(proto _c);
 control c(out bit<32> x) {
-    bit<8> a;
-    bit<16> b;
     apply {
-        a = 8w0xf;
-        b = 16w0xf;
-        x = a ++ b ++ a + (b ++ (a ++ a));
+        x = 8w0xf ++ 16w0xf ++ 8w0xf + (16w0xf ++ (8w0xf ++ 8w0xf));
     }
 }
 top(c()) main;
