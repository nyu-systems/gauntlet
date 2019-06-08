--- before_pass
+++ after_pass
@@ -190,10 +190,20 @@ struct headers {
     ipv4_t     ipv4;
 }
 parser EgressParserImpl(packet_in buffer, out headers parsed_hdr, inout metadata user_meta, in psa_egress_parser_input_metadata_t istd, out psa_parser_output_metadata_t ostd) {
-    headers parsed_hdr_2;
-    metadata user_meta_3;
-    psa_egress_parser_input_metadata_t istd_1;
-    metadata user_meta_4;
+    ethernet_t parsed_hdr_2_ethernet;
+    ipv4_t parsed_hdr_2_ipv4;
+    fwd_metadata_t user_meta_3_fwd_metadata;
+    bit<3> user_meta_3_custom_clone_id;
+    clone_0_t user_meta_3_clone;
+    clone_1_t user_meta_3_clone_0;
+    bit<10> istd_1_egress_port;
+    bit<32> istd_1_instance_type;
+    bit<3> istd_1_clone_metadata_type;
+    clone_union_t istd_1_clone_metadata_data;
+    fwd_metadata_t user_meta_4_fwd_metadata;
+    bit<3> user_meta_4_custom_clone_id;
+    clone_0_t user_meta_4_clone;
+    clone_1_t user_meta_4_clone_0;
     state start {
         transition select(istd.instance_type) {
             32w1: parse_clone_header;
@@ -201,85 +211,85 @@ parser EgressParserImpl(packet_in buffer
         }
     }
     state parse_ethernet {
-        parsed_hdr_2.ethernet.setInvalid();
-        parsed_hdr_2.ipv4.setInvalid();
+        parsed_hdr_2_ethernet.setInvalid();
+        parsed_hdr_2_ipv4.setInvalid();
         {
             {
-                user_meta_3.fwd_metadata.outport = user_meta.fwd_metadata.outport;
+                user_meta_3_fwd_metadata.outport = user_meta.fwd_metadata.outport;
             }
-            user_meta_3.custom_clone_id = user_meta.custom_clone_id;
-            user_meta_3.clone_0 = user_meta.clone_0;
-            user_meta_3.clone_1 = user_meta.clone_1;
+            user_meta_3_custom_clone_id = user_meta.custom_clone_id;
+            user_meta_3_clone = user_meta.clone_0;
+            user_meta_3_clone_0 = user_meta.clone_1;
         }
-        buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
-        transition select(parsed_hdr_2.ethernet.etherType) {
+        buffer.extract<ethernet_t>(parsed_hdr_2_ethernet);
+        transition select(parsed_hdr_2_ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4;
             default: parse_ethernet_0;
         }
     }
     state CommonParser_parse_ipv4 {
-        buffer.extract<ipv4_t>(parsed_hdr_2.ipv4);
+        buffer.extract<ipv4_t>(parsed_hdr_2_ipv4);
         transition parse_ethernet_0;
     }
     state parse_ethernet_0 {
         {
-            parsed_hdr.ethernet = parsed_hdr_2.ethernet;
-            parsed_hdr.ipv4 = parsed_hdr_2.ipv4;
+            parsed_hdr.ethernet = parsed_hdr_2_ethernet;
+            parsed_hdr.ipv4 = parsed_hdr_2_ipv4;
         }
         {
             {
-                user_meta.fwd_metadata.outport = user_meta_3.fwd_metadata.outport;
+                user_meta.fwd_metadata.outport = user_meta_3_fwd_metadata.outport;
             }
-            user_meta.custom_clone_id = user_meta_3.custom_clone_id;
-            user_meta.clone_0 = user_meta_3.clone_0;
-            user_meta.clone_1 = user_meta_3.clone_1;
+            user_meta.custom_clone_id = user_meta_3_custom_clone_id;
+            user_meta.clone_0 = user_meta_3_clone;
+            user_meta.clone_1 = user_meta_3_clone_0;
         }
         transition accept;
     }
     state parse_clone_header {
         {
-            istd_1.egress_port = istd.egress_port;
-            istd_1.instance_type = istd.instance_type;
+            istd_1_egress_port = istd.egress_port;
+            istd_1_instance_type = istd.instance_type;
             {
-                istd_1.clone_metadata.type = istd.clone_metadata.type;
+                istd_1_clone_metadata_type = istd.clone_metadata.type;
                 {
-                    istd_1.clone_metadata.data.h0 = istd.clone_metadata.data.h0;
-                    istd_1.clone_metadata.data.h1 = istd.clone_metadata.data.h1;
+                    istd_1_clone_metadata_data.h0 = istd.clone_metadata.data.h0;
+                    istd_1_clone_metadata_data.h1 = istd.clone_metadata.data.h1;
                 }
             }
         }
         {
             {
-                user_meta_4.fwd_metadata.outport = user_meta.fwd_metadata.outport;
+                user_meta_4_fwd_metadata.outport = user_meta.fwd_metadata.outport;
             }
-            user_meta_4.custom_clone_id = user_meta.custom_clone_id;
-            user_meta_4.clone_0 = user_meta.clone_0;
-            user_meta_4.clone_1 = user_meta.clone_1;
+            user_meta_4_custom_clone_id = user_meta.custom_clone_id;
+            user_meta_4_clone = user_meta.clone_0;
+            user_meta_4_clone_0 = user_meta.clone_1;
         }
-        transition select(istd_1.clone_metadata.type) {
+        transition select(istd_1_clone_metadata_type) {
             3w0: CloneParser_parse_clone_header;
             3w1: CloneParser_parse_clone_header_0;
             default: reject;
         }
     }
     state CloneParser_parse_clone_header {
-        user_meta_4.custom_clone_id = istd_1.clone_metadata.type;
-        user_meta_4.clone_0 = istd_1.clone_metadata.data.h0;
+        user_meta_4_custom_clone_id = istd_1_clone_metadata_type;
+        user_meta_4_clone = istd_1_clone_metadata_data.h0;
         transition parse_clone_header_2;
     }
     state CloneParser_parse_clone_header_0 {
-        user_meta_4.custom_clone_id = istd_1.clone_metadata.type;
-        user_meta_4.clone_1 = istd_1.clone_metadata.data.h1;
+        user_meta_4_custom_clone_id = istd_1_clone_metadata_type;
+        user_meta_4_clone_0 = istd_1_clone_metadata_data.h1;
         transition parse_clone_header_2;
     }
     state parse_clone_header_2 {
         {
             {
-                user_meta.fwd_metadata.outport = user_meta_4.fwd_metadata.outport;
+                user_meta.fwd_metadata.outport = user_meta_4_fwd_metadata.outport;
             }
-            user_meta.custom_clone_id = user_meta_4.custom_clone_id;
-            user_meta.clone_0 = user_meta_4.clone_0;
-            user_meta.clone_1 = user_meta_4.clone_1;
+            user_meta.custom_clone_id = user_meta_4_custom_clone_id;
+            user_meta.clone_0 = user_meta_4_clone;
+            user_meta.clone_1 = user_meta_4_clone_0;
         }
         transition parse_ethernet;
     }
@@ -309,41 +319,45 @@ control egress(inout headers hdr, inout
     }
 }
 parser IngressParserImpl(packet_in buffer, out headers parsed_hdr, inout metadata user_meta, in psa_ingress_parser_input_metadata_t istd, out psa_parser_output_metadata_t ostd) {
-    headers parsed_hdr_3;
-    metadata user_meta_5;
+    ethernet_t parsed_hdr_3_ethernet;
+    ipv4_t parsed_hdr_3_ipv4;
+    fwd_metadata_t user_meta_5_fwd_metadata;
+    bit<3> user_meta_5_custom_clone_id;
+    clone_0_t user_meta_5_clone;
+    clone_1_t user_meta_5_clone_0;
     state start {
-        parsed_hdr_3.ethernet.setInvalid();
-        parsed_hdr_3.ipv4.setInvalid();
+        parsed_hdr_3_ethernet.setInvalid();
+        parsed_hdr_3_ipv4.setInvalid();
         {
             {
-                user_meta_5.fwd_metadata.outport = user_meta.fwd_metadata.outport;
+                user_meta_5_fwd_metadata.outport = user_meta.fwd_metadata.outport;
             }
-            user_meta_5.custom_clone_id = user_meta.custom_clone_id;
-            user_meta_5.clone_0 = user_meta.clone_0;
-            user_meta_5.clone_1 = user_meta.clone_1;
+            user_meta_5_custom_clone_id = user_meta.custom_clone_id;
+            user_meta_5_clone = user_meta.clone_0;
+            user_meta_5_clone_0 = user_meta.clone_1;
         }
-        buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
-        transition select(parsed_hdr_3.ethernet.etherType) {
+        buffer.extract<ethernet_t>(parsed_hdr_3_ethernet);
+        transition select(parsed_hdr_3_ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4_0;
             default: start_0;
         }
     }
     state CommonParser_parse_ipv4_0 {
-        buffer.extract<ipv4_t>(parsed_hdr_3.ipv4);
+        buffer.extract<ipv4_t>(parsed_hdr_3_ipv4);
         transition start_0;
     }
     state start_0 {
         {
-            parsed_hdr.ethernet = parsed_hdr_3.ethernet;
-            parsed_hdr.ipv4 = parsed_hdr_3.ipv4;
+            parsed_hdr.ethernet = parsed_hdr_3_ethernet;
+            parsed_hdr.ipv4 = parsed_hdr_3_ipv4;
         }
         {
             {
-                user_meta.fwd_metadata.outport = user_meta_5.fwd_metadata.outport;
+                user_meta.fwd_metadata.outport = user_meta_5_fwd_metadata.outport;
             }
-            user_meta.custom_clone_id = user_meta_5.custom_clone_id;
-            user_meta.clone_0 = user_meta_5.clone_0;
-            user_meta.clone_1 = user_meta_5.clone_1;
+            user_meta.custom_clone_id = user_meta_5_custom_clone_id;
+            user_meta.clone_0 = user_meta_5_clone;
+            user_meta.clone_1 = user_meta_5_clone_0;
         }
         transition accept;
     }
@@ -371,18 +385,19 @@ control ingress(inout headers hdr, inout
     }
 }
 control IngressDeparserImpl(packet_out packet, inout headers hdr, in metadata meta, in psa_ingress_output_metadata_t istd, out psa_ingress_deparser_output_metadata_t ostd) {
-    clone_metadata_t clone_md;
+    bit<3> clone_md_type;
+    clone_union_t clone_md_data;
     apply {
-        clone_md.data.h1.setValid();
+        clone_md_data.h1.setValid();
         {
-            clone_md.data.h1.data = 32w0;
+            clone_md_data.h1.data = 32w0;
         }
-        clone_md.type = 3w0;
+        clone_md_type = 3w0;
         if (meta.custom_clone_id == 3w1) {
-            ostd.clone_metadata.type = clone_md.type;
+            ostd.clone_metadata.type = clone_md_type;
             {
-                ostd.clone_metadata.data.h0 = clone_md.data.h0;
-                ostd.clone_metadata.data.h1 = clone_md.data.h1;
+                ostd.clone_metadata.data.h0 = clone_md_data.h0;
+                ostd.clone_metadata.data.h1 = clone_md_data.h1;
             }
         }
         packet.emit<ethernet_t>(hdr.ethernet);
