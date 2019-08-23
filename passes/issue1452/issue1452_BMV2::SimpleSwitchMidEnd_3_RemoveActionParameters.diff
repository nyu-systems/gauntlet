--- before_pass
+++ after_pass
@@ -1,12 +1,16 @@
 control c() {
     bit<32> x_0;
-    @name("c.a") action a(inout bit<32> arg) {
-        bool hasReturned = false;
+    bool hasReturned;
+    bit<32> arg;
+    @name("c.a") action a() {
+        arg = x_0;
+        hasReturned = false;
         arg = 32w1;
         hasReturned = true;
+        x_0 = arg;
     }
     apply {
-        a(x_0);
+        a();
     }
 }
 control proto();
