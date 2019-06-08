--- before_pass
+++ after_pass
@@ -1,5 +1,4 @@
 control ctrl(out bit<32> c) {
-    bit<32> a;
     @name("ctrl.e") action e_0() {
         exit;
     }
@@ -7,9 +6,8 @@ control ctrl(out bit<32> c) {
         exit;
     }
     apply {
-        a = 32w0;
         c = 32w2;
-        if (a == 32w0) 
+        if (32w0 == 32w0) 
             e_0();
         else 
             e_2();
