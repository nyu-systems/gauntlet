--- before_pass
+++ after_pass
@@ -14,8 +14,11 @@ struct row_t {
 struct parsed_packet_t {
 }
 struct local_metadata_t {
-    short s;
-    row_t row;
+    short  _s0;
+    bit<1> _row_alt0_valid1;
+    bit<7> _row_alt0_port2;
+    bit<1> _row_alt1_valid3;
+    bit<7> _row_alt1_port4;
 }
 parser parse(packet_in pk, out parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
     state start {
@@ -24,15 +27,15 @@ parser parse(packet_in pk, out parsed_pa
 }
 control ingress(inout parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
     apply {
-        local_metadata.s.setValid();
-        local_metadata.s.f = 32w0;
+        local_metadata._s0.setValid();
+        local_metadata._s0.f = 32w0;
         {
-            local_metadata.row.alt0.valid = local_metadata.row.alt1.valid;
-            local_metadata.row.alt0.port = local_metadata.row.alt1.port;
+            local_metadata._row_alt0_valid1 = local_metadata._row_alt1_valid3;
+            local_metadata._row_alt0_port2 = local_metadata._row_alt1_port4;
         }
-        local_metadata.row.alt0.valid = 1w1;
-        local_metadata.row.alt1.port = local_metadata.row.alt1.port + 7w1;
-        clone3<row_t>(CloneType.I2E, 32w0, local_metadata.row);
+        local_metadata._row_alt0_valid1 = 1w1;
+        local_metadata._row_alt1_port4 = local_metadata._row_alt1_port4 + 7w1;
+        clone3<row_t>(CloneType.I2E, 32w0, {{local_metadata._row_alt0_valid1,local_metadata._row_alt0_port2},{local_metadata._row_alt1_valid3,local_metadata._row_alt1_port4}});
     }
 }
 control egress(inout parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
