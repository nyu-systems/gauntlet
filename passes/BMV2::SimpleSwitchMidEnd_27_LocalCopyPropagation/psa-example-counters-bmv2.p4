--- before_pass
+++ after_pass
@@ -69,35 +69,15 @@ parser EgressParserImpl(packet_in buffer
     }
 }
 control ingress(inout headers hdr, inout metadata user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
-    psa_ingress_output_metadata_t meta_2;
-    PortId_t egress_port_1;
-    psa_ingress_output_metadata_t meta_3;
     @name("ingress.port_bytes_in") Counter<ByteCounter_t, PortId_t>(32w512, 32w1) port_bytes_in_0;
     @name("ingress.per_prefix_pkt_byte_count") DirectCounter<PacketByteCounter_t>(32w2) per_prefix_pkt_byte_count_0;
     @name("ingress.next_hop") action next_hop(PortId_t oport) {
         per_prefix_pkt_byte_count_0.count();
         {
             {
-                meta_2.class_of_service = ostd.class_of_service;
-                meta_2.clone = ostd.clone;
-                meta_2.clone_session_id = ostd.clone_session_id;
-                meta_2.drop = ostd.drop;
-                meta_2.resubmit = ostd.resubmit;
-                meta_2.multicast_group = ostd.multicast_group;
-                meta_2.egress_port = ostd.egress_port;
-            }
-            egress_port_1 = oport;
-            meta_2.drop = false;
-            meta_2.multicast_group = 32w0;
-            meta_2.egress_port = egress_port_1;
-            {
-                ostd.class_of_service = meta_2.class_of_service;
-                ostd.clone = meta_2.clone;
-                ostd.clone_session_id = meta_2.clone_session_id;
-                ostd.drop = meta_2.drop;
-                ostd.resubmit = meta_2.resubmit;
-                ostd.multicast_group = meta_2.multicast_group;
-                ostd.egress_port = meta_2.egress_port;
+                ostd.drop = false;
+                ostd.multicast_group = 32w0;
+                ostd.egress_port = oport;
             }
         }
     }
@@ -105,23 +85,7 @@ control ingress(inout headers hdr, inout
         per_prefix_pkt_byte_count_0.count();
         {
             {
-                meta_3.class_of_service = ostd.class_of_service;
-                meta_3.clone = ostd.clone;
-                meta_3.clone_session_id = ostd.clone_session_id;
-                meta_3.drop = ostd.drop;
-                meta_3.resubmit = ostd.resubmit;
-                meta_3.multicast_group = ostd.multicast_group;
-                meta_3.egress_port = ostd.egress_port;
-            }
-            meta_3.drop = true;
-            {
-                ostd.class_of_service = meta_3.class_of_service;
-                ostd.clone = meta_3.clone;
-                ostd.clone_session_id = meta_3.clone_session_id;
-                ostd.drop = meta_3.drop;
-                ostd.resubmit = meta_3.resubmit;
-                ostd.multicast_group = meta_3.multicast_group;
-                ostd.egress_port = meta_3.egress_port;
+                ostd.drop = true;
             }
         }
     }
