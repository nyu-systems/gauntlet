--- before_pass
+++ after_pass
@@ -5,11 +5,9 @@ header H {
 control c(inout bit<32> r) {
     H[2] h;
     bit<32> tmp_1;
-    bit<32> tmp_2;
     apply {
         tmp_1 = f(32w2);
-        tmp_2 = tmp_1;
-        h[tmp_2].setValid();
+        h[tmp_1].setValid();
     }
 }
 control simple(inout bit<32> r);
