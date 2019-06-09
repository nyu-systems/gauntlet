--- before_pass
+++ after_pass
@@ -4,22 +4,16 @@ extern Fake {
     void call(in bit<32> data);
 }
 parser P() {
-    bit<32> x_0;
     @name("P.fake") Fake() fake_0;
     state start {
-        x_0 = 32w0;
-        fake_0.call(x_0);
+        fake_0.call(32w0);
         transition accept;
     }
 }
 control C() {
-    bit<32> x_1;
-    bit<32> y_0;
     @name("C.fake") Fake() fake_1;
     apply {
-        x_1 = 32w0;
-        y_0 = x_1 + 32w1;
-        fake_1.call(y_0);
+        fake_1.call(32w0 + 32w1);
     }
 }
 parser SimpleParser();
