--- before_pass
+++ after_pass
@@ -5,11 +5,9 @@ header H {
 control c(inout bit<32> r) {
     H[2] h_0;
     bit<32> tmp;
-    bit<32> tmp_0;
     apply {
         tmp = f(32w2);
-        tmp_0 = tmp;
-        h_0[tmp_0].setValid();
+        h_0[tmp].setValid();
     }
 }
 control simple(inout bit<32> r);
