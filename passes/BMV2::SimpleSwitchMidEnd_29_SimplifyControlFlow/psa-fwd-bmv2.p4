--- before_pass
+++ after_pass
@@ -21,18 +21,8 @@ parser IngressParserImpl(packet_in buffe
     fwd_metadata_t user_meta_2_fwd_metadata;
     state start {
         parsed_hdr_2_ethernet.setInvalid();
-        {
-            {
-            }
-        }
         buffer.extract<ethernet_t>(parsed_hdr_2_ethernet);
-        {
-            parsed_hdr.ethernet = parsed_hdr_2_ethernet;
-        }
-        {
-            {
-            }
-        }
+        parsed_hdr.ethernet = parsed_hdr_2_ethernet;
         transition accept;
     }
 }
@@ -41,18 +31,8 @@ parser EgressParserImpl(packet_in buffer
     fwd_metadata_t user_meta_3_fwd_metadata;
     state start {
         parsed_hdr_3_ethernet.setInvalid();
-        {
-            {
-            }
-        }
         buffer.extract<ethernet_t>(parsed_hdr_3_ethernet);
-        {
-            parsed_hdr.ethernet = parsed_hdr_3_ethernet;
-        }
-        {
-            {
-            }
-        }
+        parsed_hdr.ethernet = parsed_hdr_3_ethernet;
         transition accept;
     }
 }
