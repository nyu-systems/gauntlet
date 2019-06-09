--- before_pass
+++ after_pass
@@ -8,7 +8,11 @@ struct row_t {
     bit<8>  v;
 }
 header hdr {
-    row_t row;
+    bit<8>  _row_e0;
+    bit<16> _row_t1;
+    bit<8>  _row_l2;
+    bit<8>  _row_r3;
+    bit<8>  _row_v4;
 }
 struct Header_t {
     hdr h;
@@ -47,7 +51,7 @@ control ingress(inout Header_t h, inout
     }
     @name("ingress.t_exact") table t_exact_0 {
         key = {
-            h.h.row.e: exact @name("h.h.row.e") ;
+            h.h._row_e0: exact @name("h.h.row.e") ;
         }
         actions = {
             a();
