--- before_pass
+++ after_pass
@@ -11,7 +11,10 @@ struct row_t {
 struct parsed_packet_t {
 }
 struct local_metadata_t {
-    row_t row;
+    bit<1> _row_alt0_valid0;
+    bit<7> _row_alt0_port1;
+    bit<1> _row_alt1_valid2;
+    bit<7> _row_alt1_port3;
 }
 parser parse(packet_in pk, out parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
     state start {
@@ -21,12 +24,12 @@ parser parse(packet_in pk, out parsed_pa
 control ingress(inout parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
     apply {
         {
-            local_metadata.row.alt0.valid = local_metadata.row.alt1.valid;
-            local_metadata.row.alt0.port = local_metadata.row.alt1.port;
+            local_metadata._row_alt0_valid0 = local_metadata._row_alt1_valid2;
+            local_metadata._row_alt0_port1 = local_metadata._row_alt1_port3;
         }
-        local_metadata.row.alt0.valid = 1w1;
-        local_metadata.row.alt1.port = local_metadata.row.alt1.port + 7w1;
-        clone3<row_t>(CloneType.I2E, 32w0, local_metadata.row);
+        local_metadata._row_alt0_valid0 = 1w1;
+        local_metadata._row_alt1_port3 = local_metadata._row_alt1_port3 + 7w1;
+        clone3<row_t>(CloneType.I2E, 32w0, {{local_metadata._row_alt0_valid0,local_metadata._row_alt0_port1},{local_metadata._row_alt1_valid2,local_metadata._row_alt1_port3}});
     }
 }
 control egress(inout parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
