--- dumps/pruned/std_meta_inlining-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:34:04.235337500 +0200
+++ dumps/pruned/std_meta_inlining-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:34:04.237187000 +0200
@@ -15,11 +15,7 @@ control DeparserImpl(packet_out packet,
 }
 control ingress(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
     @name(".send_to_cpu") action send_to_cpu() {
-        {
-        }
-        {
-            standard_metadata.egress_spec = 9w64;
-        }
+        standard_metadata.egress_spec = 9w64;
     }
     @name(".NoAction") action NoAction_0() {
     }
