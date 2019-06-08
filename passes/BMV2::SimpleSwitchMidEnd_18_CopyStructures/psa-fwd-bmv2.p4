--- dumps/pruned/psa-fwd-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:33:19.372033000 +0200
+++ dumps/pruned/psa-fwd-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:33:19.380943400 +0200
@@ -21,10 +21,18 @@ parser IngressParserImpl(packet_in buffe
     metadata user_meta_2;
     state start {
         parsed_hdr_2.ethernet.setInvalid();
-        user_meta_2 = user_meta;
+        {
+            {
+            }
+        }
         buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
-        parsed_hdr = parsed_hdr_2;
-        user_meta = user_meta_2;
+        {
+            parsed_hdr.ethernet = parsed_hdr_2.ethernet;
+        }
+        {
+            {
+            }
+        }
         transition accept;
     }
 }
@@ -33,10 +41,18 @@ parser EgressParserImpl(packet_in buffer
     metadata user_meta_3;
     state start {
         parsed_hdr_3.ethernet.setInvalid();
-        user_meta_3 = user_meta;
+        {
+            {
+            }
+        }
         buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
-        parsed_hdr = parsed_hdr_3;
-        user_meta = user_meta_3;
+        {
+            parsed_hdr.ethernet = parsed_hdr_3.ethernet;
+        }
+        {
+            {
+            }
+        }
         transition accept;
     }
 }
