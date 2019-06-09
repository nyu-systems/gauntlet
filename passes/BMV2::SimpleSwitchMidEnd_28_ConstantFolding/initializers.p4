--- before_pass
+++ after_pass
@@ -13,7 +13,7 @@ parser P() {
 control C() {
     @name("C.fake") Fake() fake_1;
     apply {
-        fake_1.call(32w0 + 32w1);
+        fake_1.call(32w1);
     }
 }
 parser SimpleParser();
