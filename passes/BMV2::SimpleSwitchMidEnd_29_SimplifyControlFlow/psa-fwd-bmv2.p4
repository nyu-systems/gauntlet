--- dumps/pruned/psa-fwd-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:33:19.438615100 +0200
+++ dumps/pruned/psa-fwd-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:33:19.522213200 +0200
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
