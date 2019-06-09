--- before_pass
+++ after_pass
@@ -15,9 +15,11 @@ struct Flags {
     bit<6> pad;
 }
 header Nested {
-    Flags      flags;
-    bit<32>    b;
-    varbit<32> v;
+    bit<1>     _flags_f00;
+    bit<1>     _flags_f11;
+    bit<6>     _flags_pad2;
+    bit<32>    _b3;
+    varbit<32> _v4;
 }
 struct S {
     H    h1;
