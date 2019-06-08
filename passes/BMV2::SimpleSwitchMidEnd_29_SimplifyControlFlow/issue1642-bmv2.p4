--- dumps/pruned/issue1642-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:07.684002300 +0200
+++ dumps/pruned/issue1642-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:07.723243500 +0200
@@ -26,10 +26,8 @@ control ingress(inout parsed_packet_t hd
     apply {
         local_metadata.s.setValid();
         local_metadata.s.f = 32w0;
-        {
-            local_metadata.row.alt0.valid = local_metadata.row.alt1.valid;
-            local_metadata.row.alt0.port = local_metadata.row.alt1.port;
-        }
+        local_metadata.row.alt0.valid = local_metadata.row.alt1.valid;
+        local_metadata.row.alt0.port = local_metadata.row.alt1.port;
         local_metadata.row.alt0.valid = 1w1;
         local_metadata.row.alt1.port = local_metadata.row.alt1.port + 7w1;
         clone3<row_t>(CloneType.I2E, 32w0, local_metadata.row);
