--- before_pass
+++ after_pass
@@ -11,7 +11,7 @@ struct m {
 parser MyParser(packet_in b, out h hdrs, inout m meta, inout standard_metadata_t std) {
     state start {
         meta.counter = 3w4;
-        meta.counter = meta.counter + 3w7;
+        meta.counter = 3w4 + 3w7;
         transition accept;
     }
 }
