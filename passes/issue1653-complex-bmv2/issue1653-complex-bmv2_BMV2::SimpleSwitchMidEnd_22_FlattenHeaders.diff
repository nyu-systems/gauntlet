--- before_pass
+++ after_pass
@@ -13,7 +13,18 @@ struct row_t {
     alt_t alt1;
 }
 header bitvec_hdr {
-    row_t row;
+    bit<1>  _row_alt0_valid0;
+    bit<7>  _row_alt0_port1;
+    int<8>  _row_alt0_hashRes2;
+    bool    _row_alt0_useHash3;
+    bit<16> _row_alt0_type4;
+    bit<7>  _row_alt0_pad5;
+    bit<1>  _row_alt1_valid6;
+    bit<7>  _row_alt1_port7;
+    int<8>  _row_alt1_hashRes8;
+    bool    _row_alt1_useHash9;
+    bit<16> _row_alt1_type10;
+    bit<7>  _row_alt1_pad11;
 }
 struct local_metadata_t {
     row_t      row0;
@@ -37,12 +48,12 @@ control ingress(inout parsed_packet_t h,
     @name(".NoAction") action NoAction_0() {
     }
     @name("ingress.do_act") action do_act() {
-        h.bvh1.row.alt1.valid = 1w0;
+        h.bvh1._row_alt1_valid6 = 1w0;
         local_metadata.row0.alt0.valid = 1w0;
     }
     @name("ingress.tns") table tns_0 {
         key = {
-            h.bvh1.row.alt1.valid         : exact @name("h.bvh1.row.alt1.valid") ;
+            h.bvh1._row_alt1_valid6       : exact @name("h.bvh1.row.alt1.valid") ;
             local_metadata.row0.alt0.valid: exact @name("local_metadata.row0.alt0.valid") ;
         }
         actions = {
@@ -53,8 +64,8 @@ control ingress(inout parsed_packet_t h,
     }
     apply {
         tns_0.apply();
-        bh_0.row.alt1.type = 16w0x800;
-        h.bvh0.row.alt1.type = bh_0.row.alt1.type;
+        bh_0._row_alt1_type10 = 16w0x800;
+        h.bvh0._row_alt1_type10 = bh_0._row_alt1_type10;
         local_metadata.row0.alt0.useHash = true;
         clone3<row_t>(CloneType.I2E, 32w0, local_metadata.row0);
     }
