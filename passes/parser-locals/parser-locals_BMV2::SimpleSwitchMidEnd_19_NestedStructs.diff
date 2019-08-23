--- before_pass
+++ after_pass
@@ -9,10 +9,12 @@ struct S {
     bit<32> c;
 }
 parser p() {
-    S s_0;
+    H s_0_h1;
+    H s_0_h2;
+    bit<32> s_0_c;
     state start {
-        s_0.h1.setInvalid();
-        s_0.h2.setInvalid();
+        s_0_h1.setInvalid();
+        s_0_h2.setInvalid();
         transition accept;
     }
 }
