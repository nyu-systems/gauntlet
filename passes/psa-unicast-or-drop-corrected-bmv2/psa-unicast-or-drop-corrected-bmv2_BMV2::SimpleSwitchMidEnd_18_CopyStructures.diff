--- before_pass
+++ after_pass
@@ -23,18 +23,50 @@ control cIngress(inout headers_t hdr, in
     psa_ingress_output_metadata_t meta_2;
     PortId_t egress_port_1;
     @name(".send_to_port") action send_to_port() {
-        meta_2 = ostd;
+        {
+            meta_2.class_of_service = ostd.class_of_service;
+            meta_2.clone = ostd.clone;
+            meta_2.clone_session_id = ostd.clone_session_id;
+            meta_2.drop = ostd.drop;
+            meta_2.resubmit = ostd.resubmit;
+            meta_2.multicast_group = ostd.multicast_group;
+            meta_2.egress_port = ostd.egress_port;
+        }
         egress_port_1 = (PortIdUint_t)hdr.ethernet.dstAddr;
         meta_2.drop = false;
         meta_2.multicast_group = 32w0;
         meta_2.egress_port = egress_port_1;
-        ostd = meta_2;
+        {
+            ostd.class_of_service = meta_2.class_of_service;
+            ostd.clone = meta_2.clone;
+            ostd.clone_session_id = meta_2.clone_session_id;
+            ostd.drop = meta_2.drop;
+            ostd.resubmit = meta_2.resubmit;
+            ostd.multicast_group = meta_2.multicast_group;
+            ostd.egress_port = meta_2.egress_port;
+        }
     }
     psa_ingress_output_metadata_t meta_3;
     @name(".ingress_drop") action ingress_drop() {
-        meta_3 = ostd;
+        {
+            meta_3.class_of_service = ostd.class_of_service;
+            meta_3.clone = ostd.clone;
+            meta_3.clone_session_id = ostd.clone_session_id;
+            meta_3.drop = ostd.drop;
+            meta_3.resubmit = ostd.resubmit;
+            meta_3.multicast_group = ostd.multicast_group;
+            meta_3.egress_port = ostd.egress_port;
+        }
         meta_3.drop = true;
-        ostd = meta_3;
+        {
+            ostd.class_of_service = meta_3.class_of_service;
+            ostd.clone = meta_3.clone;
+            ostd.clone_session_id = meta_3.clone_session_id;
+            ostd.drop = meta_3.drop;
+            ostd.resubmit = meta_3.resubmit;
+            ostd.multicast_group = meta_3.multicast_group;
+            ostd.egress_port = meta_3.egress_port;
+        }
     }
     apply {
         send_to_port();
