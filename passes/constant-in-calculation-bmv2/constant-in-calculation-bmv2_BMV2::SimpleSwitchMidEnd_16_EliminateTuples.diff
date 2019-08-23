--- before_pass
+++ after_pass
@@ -31,9 +31,12 @@ control deparser(packet_out b, in Header
         b.emit<hdr>(h.h);
     }
 }
+struct tuple_0 {
+    bit<16> field;
+}
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
     apply {
-        hash<bit<16>, bit<10>, tuple<bit<16>>, bit<10>>(h.h.a, HashAlgorithm.crc16, 10w0, { 16w1 }, 10w4);
+        hash<bit<16>, bit<10>, tuple_0, bit<10>>(h.h.a, HashAlgorithm.crc16, 10w0, { 16w1 }, 10w4);
         sm.egress_spec = 9w0;
     }
 }
