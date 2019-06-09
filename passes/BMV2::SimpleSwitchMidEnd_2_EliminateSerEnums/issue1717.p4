--- before_pass
+++ after_pass
@@ -2,15 +2,12 @@ header H {
     bit<32> isValid;
 }
 typedef bit<32> T;
-enum bit<16> E {
-    z = 16w0
-}
 header H1 {
     bit<16> f;
     bit<8>  minSizeInBytes;
     bit<8>  minSizeInBits;
     T       f1;
-    E       e;
+    bit<16> e;
 }
 struct Flags {
     bit<1> f0;
