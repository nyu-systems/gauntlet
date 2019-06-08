--- before_pass
+++ after_pass
@@ -15,7 +15,7 @@ parser P() {
 control C() {
     @name("C.fake") Fake() fake_2;
     apply {
-        fake_2.call(32w0 + 32w1);
+        fake_2.call(32w1);
     }
 }
 parser SimpleParser();
