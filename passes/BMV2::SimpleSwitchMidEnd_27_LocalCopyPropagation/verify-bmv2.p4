--- before_pass
+++ after_pass
@@ -9,12 +9,10 @@ struct m {
 struct h {
 }
 parser MyParser(packet_in b, out h hdr, inout m meta, inout standard_metadata_t std) {
-    error e_0;
     state start {
         verify(meta.x == 8s0, error.NewError);
         verify(true, error.NoError);
-        e_0 = error.NoError;
-        verify(true, e_0);
+        verify(true, error.NoError);
         transition accept;
     }
 }
