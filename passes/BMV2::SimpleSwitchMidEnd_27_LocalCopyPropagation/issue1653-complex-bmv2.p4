--- before_pass
+++ after_pass
@@ -66,7 +66,6 @@ parser parse(packet_in pk, out parsed_pa
     }
 }
 control ingress(inout parsed_packet_t h, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
-    bitvec_hdr bh_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("ingress.do_act") action do_act() {
@@ -86,10 +85,9 @@ control ingress(inout parsed_packet_t h,
     }
     apply {
         tns_0.apply();
-        bh_0._row_alt1_type10 = 16w0x800;
-        h.bvh0._row_alt1_type10 = bh_0._row_alt1_type10;
+        h.bvh0._row_alt1_type10 = 16w0x800;
         local_metadata._row0_alt0_useHash3 = true;
-        clone3<row_t>(CloneType.I2E, 32w0, {{local_metadata._row0_alt0_valid0,local_metadata._row0_alt0_port1,local_metadata._row0_alt0_hashRes2,local_metadata._row0_alt0_useHash3,local_metadata._row0_alt0_type4,local_metadata._row0_alt0_pad5},{local_metadata._row0_alt1_valid6,local_metadata._row0_alt1_port7,local_metadata._row0_alt1_hashRes8,local_metadata._row0_alt1_useHash9,local_metadata._row0_alt1_type10,local_metadata._row0_alt1_pad11}});
+        clone3<row_t>(CloneType.I2E, 32w0, {{local_metadata._row0_alt0_valid0,local_metadata._row0_alt0_port1,local_metadata._row0_alt0_hashRes2,true,local_metadata._row0_alt0_type4,local_metadata._row0_alt0_pad5},{local_metadata._row0_alt1_valid6,local_metadata._row0_alt1_port7,local_metadata._row0_alt1_hashRes8,local_metadata._row0_alt1_useHash9,local_metadata._row0_alt1_type10,local_metadata._row0_alt1_pad11}});
     }
 }
 control egress(inout parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
