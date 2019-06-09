--- before_pass
+++ after_pass
@@ -5,15 +5,12 @@ extern Generic<T> {
 }
 extern void f<T>(in T arg);
 control caller() {
-    bit<5> cinst_b;
-    bit<32> cinst_tmp;
     bit<5> cinst_tmp_0;
     @name("caller.cinst.x") Generic<bit<8>>(8w9) cinst_x;
     apply {
-        cinst_tmp = cinst_x.get<bit<32>>();
+        cinst_x.get<bit<32>>();
         cinst_tmp_0 = cinst_x.get1<bit<5>, bit<10>>(10w0, 5w0);
-        cinst_b = cinst_tmp_0;
-        f<bit<5>>(cinst_b);
+        f<bit<5>>(cinst_tmp_0);
     }
 }
 control s();
