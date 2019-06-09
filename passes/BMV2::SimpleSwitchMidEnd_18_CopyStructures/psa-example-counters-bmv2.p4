--- before_pass
+++ after_pass
@@ -78,20 +78,52 @@ control ingress(inout headers hdr, inout
     @name("ingress.next_hop") action next_hop(PortId_t oport) {
         per_prefix_pkt_byte_count_0.count();
         {
-            meta_2 = ostd;
+            {
+                meta_2.class_of_service = ostd.class_of_service;
+                meta_2.clone = ostd.clone;
+                meta_2.clone_session_id = ostd.clone_session_id;
+                meta_2.drop = ostd.drop;
+                meta_2.resubmit = ostd.resubmit;
+                meta_2.multicast_group = ostd.multicast_group;
+                meta_2.egress_port = ostd.egress_port;
+            }
             egress_port_1 = oport;
             meta_2.drop = false;
             meta_2.multicast_group = 32w0;
             meta_2.egress_port = egress_port_1;
-            ostd = meta_2;
+            {
+                ostd.class_of_service = meta_2.class_of_service;
+                ostd.clone = meta_2.clone;
+                ostd.clone_session_id = meta_2.clone_session_id;
+                ostd.drop = meta_2.drop;
+                ostd.resubmit = meta_2.resubmit;
+                ostd.multicast_group = meta_2.multicast_group;
+                ostd.egress_port = meta_2.egress_port;
+            }
         }
     }
     @name("ingress.default_route_drop") action default_route_drop() {
         per_prefix_pkt_byte_count_0.count();
         {
-            meta_3 = ostd;
+            {
+                meta_3.class_of_service = ostd.class_of_service;
+                meta_3.clone = ostd.clone;
+                meta_3.clone_session_id = ostd.clone_session_id;
+                meta_3.drop = ostd.drop;
+                meta_3.resubmit = ostd.resubmit;
+                meta_3.multicast_group = ostd.multicast_group;
+                meta_3.egress_port = ostd.egress_port;
+            }
             meta_3.drop = true;
-            ostd = meta_3;
+            {
+                ostd.class_of_service = meta_3.class_of_service;
+                ostd.clone = meta_3.clone;
+                ostd.clone_session_id = meta_3.clone_session_id;
+                ostd.drop = meta_3.drop;
+                ostd.resubmit = meta_3.resubmit;
+                ostd.multicast_group = meta_3.multicast_group;
+                ostd.egress_port = meta_3.egress_port;
+            }
         }
     }
     @name("ingress.ipv4_da_lpm") table ipv4_da_lpm_0 {
