--- before_pass
+++ after_pass
@@ -9,13 +9,22 @@ struct row_t {
     alt_t alt1;
 }
 header Hdr1 {
-    bit<8> a;
-    row_t  row0;
-    row_t  row1;
+    bit<8> _a0;
+    bit<1> _row0_alt0_valid1;
+    bit<7> _row0_alt0_port2;
+    bit<1> _row0_alt1_valid3;
+    bit<7> _row0_alt1_port4;
+    bit<1> _row1_alt0_valid5;
+    bit<7> _row1_alt0_port6;
+    bit<1> _row1_alt1_valid7;
+    bit<7> _row1_alt1_port8;
 }
 header Hdr2 {
-    bit<16> b;
-    row_t   row;
+    bit<16> _b0;
+    bit<1>  _row_alt0_valid1;
+    bit<7>  _row_alt0_port2;
+    bit<1>  _row_alt1_valid3;
+    bit<7>  _row_alt1_port4;
 }
 header_union U {
     Hdr1 h1;
@@ -30,7 +39,7 @@ struct Meta {
 parser p(packet_in b, out Headers h, inout Meta m, inout standard_metadata_t sm) {
     state start {
         b.extract<Hdr1>(h.h1);
-        transition select(h.h1.a) {
+        transition select(h.h1._a0) {
             8w0: getH1;
             default: getH2;
         }
