--- before_pass
+++ after_pass
@@ -10,7 +10,6 @@ extern Overloaded {
     void f(bit<32> a, bit<16> b);
 }
 control c() {
-    bit<32> z;
     @name("c.o") Overloaded() o;
     apply {
         f();
@@ -23,7 +22,6 @@ control c() {
         o.f(b = 16w1);
         o.f(a = 32w1, b = 16w2);
         o.f(a = 32w1, b = 16w2);
-        z = 32w4294967294;
     }
 }
 control proto();
