--- before_pass
+++ after_pass
@@ -11,7 +11,7 @@ struct H {
     T s;
 }
 struct M {
-    S s;
+    bit<32> _s_x0;
 }
 control VerifyChecksumI(inout H hdr, inout M meta) {
     apply {
