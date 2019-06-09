--- before_pass
+++ after_pass
@@ -10,7 +10,6 @@ extern Overloaded {
     void f(bit<32> a, bit<16> b);
 }
 control c() {
-    bit<32> z_0;
     @name("c.o") Overloaded() o_0;
     apply {
         f();
@@ -23,7 +22,6 @@ control c() {
         o_0.f(b = 16w1);
         o_0.f(a = 32w1, b = 16w2);
         o_0.f(a = 32w1, b = 16w2);
-        z_0 = 32w4294967294;
     }
 }
 control proto();
