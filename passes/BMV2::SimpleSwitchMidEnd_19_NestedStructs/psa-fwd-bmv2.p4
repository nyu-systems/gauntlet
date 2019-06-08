--- dumps/pruned/psa-fwd-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:33:19.380943400 +0200
+++ dumps/pruned/psa-fwd-bmv2-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-06-08 18:33:19.385350400 +0200
@@ -17,17 +17,17 @@ struct headers {
     ethernet_t ethernet;
 }
 parser IngressParserImpl(packet_in buffer, out headers parsed_hdr, inout metadata user_meta, in psa_ingress_parser_input_metadata_t istd, in empty_t resubmit_meta, in empty_t recirculate_meta) {
-    headers parsed_hdr_2;
-    metadata user_meta_2;
+    ethernet_t parsed_hdr_2_ethernet;
+    fwd_metadata_t user_meta_2_fwd_metadata;
     state start {
-        parsed_hdr_2.ethernet.setInvalid();
+        parsed_hdr_2_ethernet.setInvalid();
         {
             {
             }
         }
-        buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
+        buffer.extract<ethernet_t>(parsed_hdr_2_ethernet);
         {
-            parsed_hdr.ethernet = parsed_hdr_2.ethernet;
+            parsed_hdr.ethernet = parsed_hdr_2_ethernet;
         }
         {
             {
@@ -37,17 +37,17 @@ parser IngressParserImpl(packet_in buffe
     }
 }
 parser EgressParserImpl(packet_in buffer, out headers parsed_hdr, inout metadata user_meta, in psa_egress_parser_input_metadata_t istd, in empty_t normal_meta, in empty_t clone_i2e_meta, in empty_t clone_e2e_meta) {
-    headers parsed_hdr_3;
-    metadata user_meta_3;
+    ethernet_t parsed_hdr_3_ethernet;
+    fwd_metadata_t user_meta_3_fwd_metadata;
     state start {
-        parsed_hdr_3.ethernet.setInvalid();
+        parsed_hdr_3_ethernet.setInvalid();
         {
             {
             }
         }
-        buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
+        buffer.extract<ethernet_t>(parsed_hdr_3_ethernet);
         {
-            parsed_hdr.ethernet = parsed_hdr_3.ethernet;
+            parsed_hdr.ethernet = parsed_hdr_3_ethernet;
         }
         {
             {
