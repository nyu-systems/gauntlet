--- before_pass
+++ after_pass
@@ -23,11 +23,27 @@ control cIngress(inout headers_t hdr, in
     psa_ingress_output_metadata_t meta_1;
     MulticastGroup_t multicast_group_1;
     @name(".multicast") action multicast() {
-        meta_1 = ostd;
+        {
+            meta_1.class_of_service = ostd.class_of_service;
+            meta_1.clone = ostd.clone;
+            meta_1.clone_session_id = ostd.clone_session_id;
+            meta_1.drop = ostd.drop;
+            meta_1.resubmit = ostd.resubmit;
+            meta_1.multicast_group = ostd.multicast_group;
+            meta_1.egress_port = ostd.egress_port;
+        }
         multicast_group_1 = (MulticastGroup_t)hdr.ethernet.dstAddr[31:0];
         meta_1.drop = false;
         meta_1.multicast_group = multicast_group_1;
-        ostd = meta_1;
+        {
+            ostd.class_of_service = meta_1.class_of_service;
+            ostd.clone = meta_1.clone;
+            ostd.clone_session_id = meta_1.clone_session_id;
+            ostd.drop = meta_1.drop;
+            ostd.resubmit = meta_1.resubmit;
+            ostd.multicast_group = meta_1.multicast_group;
+            ostd.egress_port = meta_1.egress_port;
+        }
     }
     apply {
         multicast();
