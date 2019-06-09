--- before_pass
+++ after_pass
@@ -18,11 +18,17 @@ struct col_t {
     bitvec_hdr bvh;
 }
 struct local_metadata_t {
-    row_t      row0;
-    row_t      row1;
-    col_t      col;
-    bitvec_hdr bvh0;
-    bitvec_hdr bvh1;
+    bit<1>     _row0_alt0_valid0;
+    bit<7>     _row0_alt0_port1;
+    bit<1>     _row0_alt1_valid2;
+    bit<7>     _row0_alt1_port3;
+    bit<1>     _row1_alt0_valid4;
+    bit<7>     _row1_alt0_port5;
+    bit<1>     _row1_alt1_valid6;
+    bit<7>     _row1_alt1_port7;
+    bitvec_hdr _col_bvh8;
+    bitvec_hdr _bvh09;
+    bitvec_hdr _bvh110;
 }
 struct parsed_packet_t {
     bitvec_hdr bvh0;
@@ -39,7 +45,7 @@ parser parse(packet_in pk, out parsed_pa
     state start {
         pk.extract<bitvec_hdr>(h.bvh0);
         pk.extract<bitvec_hdr>(h.bvh1);
-        pk.extract<bitvec_hdr>(local_metadata.col.bvh);
+        pk.extract<bitvec_hdr>(local_metadata._col_bvh8);
         transition accept;
     }
 }
@@ -51,8 +57,8 @@ control ingress(inout parsed_packet_t h,
     }
     @name("ingress.tns") table tns_0 {
         key = {
-            h.bvh1._row_alt1_valid2                : exact @name("h.bvh1.row.alt1.valid") ;
-            local_metadata.col.bvh._row_alt0_valid0: exact @name("local_metadata.col.bvh.row.alt0.valid") ;
+            h.bvh1._row_alt1_valid2                  : exact @name("h.bvh1.row.alt1.valid") ;
+            local_metadata._col_bvh8._row_alt0_valid0: exact @name("local_metadata.col.bvh.row.alt0.valid") ;
         }
         actions = {
             do_act();
@@ -62,14 +68,14 @@ control ingress(inout parsed_packet_t h,
     }
     apply {
         tns_0.apply();
-        local_metadata.col.bvh._row_alt0_valid0 = 1w0;
+        local_metadata._col_bvh8._row_alt0_valid0 = 1w0;
         {
-            local_metadata.row0.alt0.valid = local_metadata.row1.alt1.valid;
-            local_metadata.row0.alt0.port = local_metadata.row1.alt1.port;
+            local_metadata._row0_alt0_valid0 = local_metadata._row1_alt1_valid6;
+            local_metadata._row0_alt0_port1 = local_metadata._row1_alt1_port7;
         }
-        local_metadata.row1.alt0.valid = 1w1;
-        local_metadata.row1.alt1.port = local_metadata.row0.alt1.port + 7w1;
-        clone3<row_t>(CloneType.I2E, 32w0, local_metadata.row0);
+        local_metadata._row1_alt0_valid4 = 1w1;
+        local_metadata._row1_alt1_port7 = local_metadata._row0_alt1_port3 + 7w1;
+        clone3<row_t>(CloneType.I2E, 32w0, {{local_metadata._row0_alt0_valid0,local_metadata._row0_alt0_port1},{local_metadata._row0_alt1_valid2,local_metadata._row0_alt1_port3}});
     }
 }
 control egress(inout parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
