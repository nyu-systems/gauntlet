--- before_pass
+++ after_pass
@@ -12,9 +12,9 @@ parser MyParser(packet_in b, out my_pack
     bool bv_0;
     state start {
         bv_0 = true;
-        transition select(bv_0) {
-            false: next;
-            true: accept;
+        transition select((bit<1>)bv_0) {
+            (bit<1>)false: next;
+            (bit<1>)true: accept;
         }
     }
     state next {
