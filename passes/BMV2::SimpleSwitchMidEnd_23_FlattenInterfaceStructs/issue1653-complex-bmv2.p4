--- before_pass
+++ after_pass
@@ -27,10 +27,32 @@ header bitvec_hdr {
     bit<7>  _row_alt1_pad11;
 }
 struct local_metadata_t {
-    row_t      row0;
-    row_t      row1;
-    bitvec_hdr bvh0;
-    bitvec_hdr bvh1;
+    bit<1>     _row0_alt0_valid0;
+    bit<7>     _row0_alt0_port1;
+    int<8>     _row0_alt0_hashRes2;
+    bool       _row0_alt0_useHash3;
+    bit<16>    _row0_alt0_type4;
+    bit<7>     _row0_alt0_pad5;
+    bit<1>     _row0_alt1_valid6;
+    bit<7>     _row0_alt1_port7;
+    int<8>     _row0_alt1_hashRes8;
+    bool       _row0_alt1_useHash9;
+    bit<16>    _row0_alt1_type10;
+    bit<7>     _row0_alt1_pad11;
+    bit<1>     _row1_alt0_valid12;
+    bit<7>     _row1_alt0_port13;
+    int<8>     _row1_alt0_hashRes14;
+    bool       _row1_alt0_useHash15;
+    bit<16>    _row1_alt0_type16;
+    bit<7>     _row1_alt0_pad17;
+    bit<1>     _row1_alt1_valid18;
+    bit<7>     _row1_alt1_port19;
+    int<8>     _row1_alt1_hashRes20;
+    bool       _row1_alt1_useHash21;
+    bit<16>    _row1_alt1_type22;
+    bit<7>     _row1_alt1_pad23;
+    bitvec_hdr _bvh024;
+    bitvec_hdr _bvh125;
 }
 struct parsed_packet_t {
     bitvec_hdr bvh0;
@@ -49,12 +71,12 @@ control ingress(inout parsed_packet_t h,
     }
     @name("ingress.do_act") action do_act() {
         h.bvh1._row_alt1_valid6 = 1w0;
-        local_metadata.row0.alt0.valid = 1w0;
+        local_metadata._row0_alt0_valid0 = 1w0;
     }
     @name("ingress.tns") table tns_0 {
         key = {
-            h.bvh1._row_alt1_valid6       : exact @name("h.bvh1.row.alt1.valid") ;
-            local_metadata.row0.alt0.valid: exact @name("local_metadata.row0.alt0.valid") ;
+            h.bvh1._row_alt1_valid6         : exact @name("h.bvh1.row.alt1.valid") ;
+            local_metadata._row0_alt0_valid0: exact @name("local_metadata.row0.alt0.valid") ;
         }
         actions = {
             do_act();
@@ -66,8 +88,8 @@ control ingress(inout parsed_packet_t h,
         tns_0.apply();
         bh_0._row_alt1_type10 = 16w0x800;
         h.bvh0._row_alt1_type10 = bh_0._row_alt1_type10;
-        local_metadata.row0.alt0.useHash = true;
-        clone3<row_t>(CloneType.I2E, 32w0, local_metadata.row0);
+        local_metadata._row0_alt0_useHash3 = true;
+        clone3<row_t>(CloneType.I2E, 32w0, row_t {alt0 = alt_t {valid = local_metadata._row0_alt0_valid0,port = local_metadata._row0_alt0_port1,hashRes = local_metadata._row0_alt0_hashRes2,useHash = local_metadata._row0_alt0_useHash3,type = local_metadata._row0_alt0_type4,pad = local_metadata._row0_alt0_pad5},alt1 = alt_t {valid = local_metadata._row0_alt1_valid6,port = local_metadata._row0_alt1_port7,hashRes = local_metadata._row0_alt1_hashRes8,useHash = local_metadata._row0_alt1_useHash9,type = local_metadata._row0_alt1_type10,pad = local_metadata._row0_alt1_pad11}});
     }
 }
 control egress(inout parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
