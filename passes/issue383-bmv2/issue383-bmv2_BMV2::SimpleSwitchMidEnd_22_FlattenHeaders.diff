--- before_pass
+++ after_pass
@@ -9,7 +9,10 @@ struct alt_t {
     alt_t alt1;
 }
 header bitvec_hdr {
-    row_t row;
+    bit<1> _row_alt0_valid0;
+    bit<7> _row_alt0_port1;
+    bit<1> _row_alt1_valid2;
+    bit<7> _row_alt1_port3;
 }
 struct col_t {
     bitvec_hdr bvh;
@@ -44,12 +47,12 @@ control ingress(inout parsed_packet_t h,
     @name(".NoAction") action NoAction_0() {
     }
     @name("ingress.do_act") action do_act() {
-        h.bvh1.row.alt1.valid = 1w0;
+        h.bvh1._row_alt1_valid2 = 1w0;
     }
     @name("ingress.tns") table tns_0 {
         key = {
-            h.bvh1.row.alt1.valid                : exact @name("h.bvh1.row.alt1.valid") ;
-            local_metadata.col.bvh.row.alt0.valid: exact @name("local_metadata.col.bvh.row.alt0.valid") ;
+            h.bvh1._row_alt1_valid2                : exact @name("h.bvh1.row.alt1.valid") ;
+            local_metadata.col.bvh._row_alt0_valid0: exact @name("local_metadata.col.bvh.row.alt0.valid") ;
         }
         actions = {
             do_act();
@@ -59,7 +62,7 @@ control ingress(inout parsed_packet_t h,
     }
     apply {
         tns_0.apply();
-        local_metadata.col.bvh.row.alt0.valid = 1w0;
+        local_metadata.col.bvh._row_alt0_valid0 = 1w0;
         {
             local_metadata.row0.alt0.valid = local_metadata.row1.alt1.valid;
             local_metadata.row0.alt0.port = local_metadata.row1.alt1.port;
