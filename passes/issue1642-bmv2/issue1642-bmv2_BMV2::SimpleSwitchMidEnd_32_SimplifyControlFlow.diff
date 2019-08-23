--- before_pass
+++ after_pass
@@ -29,10 +29,8 @@ control ingress(inout parsed_packet_t hd
     apply {
         local_metadata._s0.setValid();
         local_metadata._s0.f = 32w0;
-        {
-            local_metadata._row_alt0_valid1 = local_metadata._row_alt1_valid3;
-            local_metadata._row_alt0_port2 = local_metadata._row_alt1_port4;
-        }
+        local_metadata._row_alt0_valid1 = local_metadata._row_alt1_valid3;
+        local_metadata._row_alt0_port2 = local_metadata._row_alt1_port4;
         local_metadata._row_alt0_valid1 = 1w1;
         local_metadata._row_alt1_port4 = local_metadata._row_alt1_port4 + 7w1;
         clone3<row_t>(CloneType.I2E, 32w0, row_t {alt0 = alt_t {valid = 1w1,port = local_metadata._row_alt0_port2},alt1 = alt_t {valid = local_metadata._row_alt1_valid3,port = local_metadata._row_alt1_port4}});
