--- before_pass
+++ after_pass
@@ -15,9 +15,7 @@ control DeparserImpl(packet_out packet,
 }
 control ingress(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
     @name(".send_to_cpu") action send_to_cpu() {
-        {
-            standard_metadata.egress_spec = 9w64;
-        }
+        standard_metadata.egress_spec = 9w64;
     }
     @name(".NoAction") action NoAction_0() {
     }
