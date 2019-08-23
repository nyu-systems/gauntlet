--- before_pass
+++ after_pass
@@ -9,8 +9,11 @@ struct row_t {
     alt_t alt1;
 }
 header hdr {
-    bit<32> f;
-    row_t   row;
+    bit<32> _f0;
+    bit<1>  _row_alt0_valid1;
+    bit<7>  _row_alt0_port2;
+    bit<1>  _row_alt1_valid3;
+    bit<7>  _row_alt1_port4;
 }
 struct Headers {
     hdr h;
@@ -43,10 +46,10 @@ control deparser(packet_out b, in Header
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
     hdr[1] c_tmp;
     apply {
-        c_tmp[0].row.alt1.valid = 1w1;
-        c_tmp[0].f = h.h.f + 32w1;
-        h.h.f = c_tmp[0].f;
-        h.h.row.alt1.valid = c_tmp[0].row.alt1.valid;
+        c_tmp[0]._row_alt1_valid3 = 1w1;
+        c_tmp[0]._f0 = h.h._f0 + 32w1;
+        h.h._f0 = c_tmp[0]._f0;
+        h.h._row_alt1_valid3 = c_tmp[0]._row_alt1_valid3;
         sm.egress_spec = 9w0;
     }
 }
