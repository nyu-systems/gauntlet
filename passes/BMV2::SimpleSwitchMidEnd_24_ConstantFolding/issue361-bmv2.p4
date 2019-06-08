--- before_pass
+++ after_pass
@@ -13,8 +13,8 @@ parser MyParser(packet_in b, out my_pack
     state start {
         bv = true;
         transition select((bit<1>)bv) {
-            (bit<1>)false: next;
-            (bit<1>)true: accept;
+            1w0: next;
+            1w1: accept;
         }
     }
     state next {
