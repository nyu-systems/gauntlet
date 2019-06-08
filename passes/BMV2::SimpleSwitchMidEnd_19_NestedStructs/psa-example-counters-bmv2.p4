--- before_pass
+++ after_pass
@@ -34,29 +34,30 @@ struct headers {
     ipv4_t     ipv4;
 }
 parser IngressParserImpl(packet_in buffer, out headers parsed_hdr, inout metadata user_meta, in psa_ingress_parser_input_metadata_t istd, in empty_metadata_t resubmit_meta, in empty_metadata_t recirculate_meta) {
-    headers parsed_hdr_2;
-    metadata user_meta_2;
+    ethernet_t parsed_hdr_2_ethernet;
+    ipv4_t parsed_hdr_2_ipv4;
+    fwd_metadata_t user_meta_2_fwd_metadata;
     state start {
-        parsed_hdr_2.ethernet.setInvalid();
-        parsed_hdr_2.ipv4.setInvalid();
+        parsed_hdr_2_ethernet.setInvalid();
+        parsed_hdr_2_ipv4.setInvalid();
         {
             {
             }
         }
-        buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
-        transition select(parsed_hdr_2.ethernet.etherType) {
+        buffer.extract<ethernet_t>(parsed_hdr_2_ethernet);
+        transition select(parsed_hdr_2_ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4;
             default: start_0;
         }
     }
     state CommonParser_parse_ipv4 {
-        buffer.extract<ipv4_t>(parsed_hdr_2.ipv4);
+        buffer.extract<ipv4_t>(parsed_hdr_2_ipv4);
         transition start_0;
     }
     state start_0 {
         {
-            parsed_hdr.ethernet = parsed_hdr_2.ethernet;
-            parsed_hdr.ipv4 = parsed_hdr_2.ipv4;
+            parsed_hdr.ethernet = parsed_hdr_2_ethernet;
+            parsed_hdr.ipv4 = parsed_hdr_2_ipv4;
         }
         {
             {
@@ -66,29 +67,30 @@ parser IngressParserImpl(packet_in buffe
     }
 }
 parser EgressParserImpl(packet_in buffer, out headers parsed_hdr, inout metadata user_meta, in psa_egress_parser_input_metadata_t istd, in empty_metadata_t normal_meta, in empty_metadata_t clone_i2e_meta, in empty_metadata_t clone_e2e_meta) {
-    headers parsed_hdr_3;
-    metadata user_meta_3;
+    ethernet_t parsed_hdr_3_ethernet;
+    ipv4_t parsed_hdr_3_ipv4;
+    fwd_metadata_t user_meta_3_fwd_metadata;
     state start {
-        parsed_hdr_3.ethernet.setInvalid();
-        parsed_hdr_3.ipv4.setInvalid();
+        parsed_hdr_3_ethernet.setInvalid();
+        parsed_hdr_3_ipv4.setInvalid();
         {
             {
             }
         }
-        buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
-        transition select(parsed_hdr_3.ethernet.etherType) {
+        buffer.extract<ethernet_t>(parsed_hdr_3_ethernet);
+        transition select(parsed_hdr_3_ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4_0;
             default: start_1;
         }
     }
     state CommonParser_parse_ipv4_0 {
-        buffer.extract<ipv4_t>(parsed_hdr_3.ipv4);
+        buffer.extract<ipv4_t>(parsed_hdr_3_ipv4);
         transition start_1;
     }
     state start_1 {
         {
-            parsed_hdr.ethernet = parsed_hdr_3.ethernet;
-            parsed_hdr.ipv4 = parsed_hdr_3.ipv4;
+            parsed_hdr.ethernet = parsed_hdr_3_ethernet;
+            parsed_hdr.ipv4 = parsed_hdr_3_ipv4;
         }
         {
             {
