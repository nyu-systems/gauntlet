--- before_pass
+++ after_pass
@@ -9,10 +9,12 @@ struct S {
     bit<32> c;
 }
 parser p() {
-    S s;
+    H s_h1;
+    H s_h2;
+    bit<32> s_c;
     state start {
-        s.h1.setInvalid();
-        s.h2.setInvalid();
+        s_h1.setInvalid();
+        s_h2.setInvalid();
         transition accept;
     }
 }
