--- dumps/pruned/std_meta_inlining-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:34:04.268131800 +0200
+++ dumps/pruned/std_meta_inlining-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:34:04.251047000 +0200
@@ -14,8 +14,11 @@ control DeparserImpl(packet_out packet,
     }
 }
 control ingress(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
-    @name(".send_to_cpu") action send_to_cpu(inout standard_metadata_t standard_metadata_1) {
+    standard_metadata_t standard_metadata_1;
+    @name(".send_to_cpu") action send_to_cpu() {
+        standard_metadata_1 = standard_metadata;
         standard_metadata_1.egress_spec = 9w64;
+        standard_metadata = standard_metadata_1;
     }
     @name(".NoAction") action NoAction_0() {
     }
@@ -24,7 +27,7 @@ control ingress(inout headers_t hdr, ino
             standard_metadata.ingress_port: ternary @name("standard_metadata.ingress_port") ;
         }
         actions = {
-            send_to_cpu(standard_metadata);
+            send_to_cpu();
             @defaultonly NoAction_0();
         }
         default_action = NoAction_0();
