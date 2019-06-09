--- before_pass
+++ after_pass
@@ -11,7 +11,6 @@ struct S {
 parser p() {
     H s_0_h1;
     H s_0_h2;
-    bit<32> s_0_c;
     state start {
         s_0_h1.setInvalid();
         s_0_h2.setInvalid();
