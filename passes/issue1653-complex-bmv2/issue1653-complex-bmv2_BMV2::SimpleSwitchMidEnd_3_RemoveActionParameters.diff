--- before_pass
+++ after_pass
@@ -33,9 +33,9 @@ parser parse(packet_in pk, out parsed_pa
     }
 }
 control ingress(inout parsed_packet_t h, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
+    bitvec_hdr bh_0;
     @name(".NoAction") action NoAction_0() {
     }
-    bitvec_hdr bh_0;
     @name("ingress.do_act") action do_act() {
         h.bvh1.row.alt1.valid = 1w0;
         local_metadata.row0.alt0.valid = 1w0;
