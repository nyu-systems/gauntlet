--- before_pass
+++ after_pass
@@ -1,13 +1,7 @@
 control c() {
     bit<32> x_0;
-    bool hasReturned;
-    bit<32> arg;
     @name("c.a") action a() {
-        arg = x_0;
-        hasReturned = false;
-        arg = 32w1;
-        hasReturned = true;
-        x_0 = arg;
+        x_0 = 32w1;
     }
     apply {
         a();
