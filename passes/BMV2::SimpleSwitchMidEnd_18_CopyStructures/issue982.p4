--- dumps/pruned/issue982-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:32:50.555983500 +0200
+++ dumps/pruned/issue982-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:32:50.557859500 +0200
@@ -203,7 +203,14 @@ parser EgressParserImpl(packet_in buffer
     state parse_ethernet {
         parsed_hdr_2.ethernet.setInvalid();
         parsed_hdr_2.ipv4.setInvalid();
-        user_meta_3 = user_meta;
+        {
+            {
+                user_meta_3.fwd_metadata.outport = user_meta.fwd_metadata.outport;
+            }
+            user_meta_3.custom_clone_id = user_meta.custom_clone_id;
+            user_meta_3.clone_0 = user_meta.clone_0;
+            user_meta_3.clone_1 = user_meta.clone_1;
+        }
         buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
         transition select(parsed_hdr_2.ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4;
@@ -215,13 +222,40 @@ parser EgressParserImpl(packet_in buffer
         transition parse_ethernet_0;
     }
     state parse_ethernet_0 {
-        parsed_hdr = parsed_hdr_2;
-        user_meta = user_meta_3;
+        {
+            parsed_hdr.ethernet = parsed_hdr_2.ethernet;
+            parsed_hdr.ipv4 = parsed_hdr_2.ipv4;
+        }
+        {
+            {
+                user_meta.fwd_metadata.outport = user_meta_3.fwd_metadata.outport;
+            }
+            user_meta.custom_clone_id = user_meta_3.custom_clone_id;
+            user_meta.clone_0 = user_meta_3.clone_0;
+            user_meta.clone_1 = user_meta_3.clone_1;
+        }
         transition accept;
     }
     state parse_clone_header {
-        istd_1 = istd;
-        user_meta_4 = user_meta;
+        {
+            istd_1.egress_port = istd.egress_port;
+            istd_1.instance_type = istd.instance_type;
+            {
+                istd_1.clone_metadata.type = istd.clone_metadata.type;
+                {
+                    istd_1.clone_metadata.data.h0 = istd.clone_metadata.data.h0;
+                    istd_1.clone_metadata.data.h1 = istd.clone_metadata.data.h1;
+                }
+            }
+        }
+        {
+            {
+                user_meta_4.fwd_metadata.outport = user_meta.fwd_metadata.outport;
+            }
+            user_meta_4.custom_clone_id = user_meta.custom_clone_id;
+            user_meta_4.clone_0 = user_meta.clone_0;
+            user_meta_4.clone_1 = user_meta.clone_1;
+        }
         transition select(istd_1.clone_metadata.type) {
             3w0: CloneParser_parse_clone_header;
             3w1: CloneParser_parse_clone_header_0;
@@ -239,7 +273,14 @@ parser EgressParserImpl(packet_in buffer
         transition parse_clone_header_2;
     }
     state parse_clone_header_2 {
-        user_meta = user_meta_4;
+        {
+            {
+                user_meta.fwd_metadata.outport = user_meta_4.fwd_metadata.outport;
+            }
+            user_meta.custom_clone_id = user_meta_4.custom_clone_id;
+            user_meta.clone_0 = user_meta_4.clone_0;
+            user_meta.clone_1 = user_meta_4.clone_1;
+        }
         transition parse_ethernet;
     }
 }
@@ -273,7 +314,14 @@ parser IngressParserImpl(packet_in buffe
     state start {
         parsed_hdr_3.ethernet.setInvalid();
         parsed_hdr_3.ipv4.setInvalid();
-        user_meta_5 = user_meta;
+        {
+            {
+                user_meta_5.fwd_metadata.outport = user_meta.fwd_metadata.outport;
+            }
+            user_meta_5.custom_clone_id = user_meta.custom_clone_id;
+            user_meta_5.clone_0 = user_meta.clone_0;
+            user_meta_5.clone_1 = user_meta.clone_1;
+        }
         buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
         transition select(parsed_hdr_3.ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4_0;
@@ -285,8 +333,18 @@ parser IngressParserImpl(packet_in buffe
         transition start_0;
     }
     state start_0 {
-        parsed_hdr = parsed_hdr_3;
-        user_meta = user_meta_5;
+        {
+            parsed_hdr.ethernet = parsed_hdr_3.ethernet;
+            parsed_hdr.ipv4 = parsed_hdr_3.ipv4;
+        }
+        {
+            {
+                user_meta.fwd_metadata.outport = user_meta_5.fwd_metadata.outport;
+            }
+            user_meta.custom_clone_id = user_meta_5.custom_clone_id;
+            user_meta.clone_0 = user_meta_5.clone_0;
+            user_meta.clone_1 = user_meta_5.clone_1;
+        }
         transition accept;
     }
 }
@@ -316,10 +374,17 @@ control IngressDeparserImpl(packet_out p
     clone_metadata_t clone_md;
     apply {
         clone_md.data.h1.setValid();
-        clone_md.data.h1 = { 32w0 };
+        {
+            clone_md.data.h1.data = 32w0;
+        }
         clone_md.type = 3w0;
-        if (meta.custom_clone_id == 3w1) 
-            ostd.clone_metadata = clone_md;
+        if (meta.custom_clone_id == 3w1) {
+            ostd.clone_metadata.type = clone_md.type;
+            {
+                ostd.clone_metadata.data.h0 = clone_md.data.h0;
+                ostd.clone_metadata.data.h1 = clone_md.data.h1;
+            }
+        }
         packet.emit<ethernet_t>(hdr.ethernet);
         packet.emit<ipv4_t>(hdr.ipv4);
     }
