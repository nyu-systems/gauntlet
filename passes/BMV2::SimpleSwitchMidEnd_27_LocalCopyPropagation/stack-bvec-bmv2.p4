--- before_pass
+++ after_pass
@@ -44,12 +44,9 @@ control deparser(packet_out b, in Header
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
-    hdr[1] c_tmp;
     apply {
-        c_tmp[0]._row_alt1_valid3 = 1w1;
-        c_tmp[0]._f0 = h.h._f0 + 32w1;
-        h.h._f0 = c_tmp[0]._f0;
-        h.h._row_alt1_valid3 = c_tmp[0]._row_alt1_valid3;
+        h.h._f0 = h.h._f0 + 32w1;
+        h.h._row_alt1_valid3 = 1w1;
         sm.egress_spec = 9w0;
     }
 }
