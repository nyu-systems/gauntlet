--- before_pass
+++ after_pass
@@ -1,5 +1,4 @@
 control ctrl(out bit<32> c) {
-    bit<32> a_0;
     @name("ctrl.e") action e() {
         exit;
     }
@@ -10,9 +9,8 @@ control ctrl(out bit<32> c) {
         default_action = e();
     }
     apply {
-        a_0 = 32w0;
         c = 32w2;
-        if (a_0 == 32w0) 
+        if (32w0 == 32w0) 
             t_0.apply();
         else 
             t_0.apply();
