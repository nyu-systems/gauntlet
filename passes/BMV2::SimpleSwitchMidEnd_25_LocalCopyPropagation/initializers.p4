--- before_pass
+++ after_pass
@@ -13,13 +13,9 @@ parser P() {
     }
 }
 control C() {
-    bit<32> x_2;
-    bit<32> y;
     @name("C.fake") Fake() fake_2;
     apply {
-        x_2 = 32w0;
-        y = x_2 + 32w1;
-        fake_2.call(y);
+        fake_2.call(32w0 + 32w1);
     }
 }
 parser SimpleParser();
