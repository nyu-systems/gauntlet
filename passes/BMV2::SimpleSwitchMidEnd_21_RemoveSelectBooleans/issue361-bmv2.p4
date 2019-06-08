--- before_pass
+++ after_pass
@@ -12,9 +12,9 @@ parser MyParser(packet_in b, out my_pack
     bool bv;
     state start {
         bv = true;
-        transition select(bv) {
-            false: next;
-            true: accept;
+        transition select((bit<1>)bv) {
+            (bit<1>)false: next;
+            (bit<1>)true: accept;
         }
     }
     state next {
