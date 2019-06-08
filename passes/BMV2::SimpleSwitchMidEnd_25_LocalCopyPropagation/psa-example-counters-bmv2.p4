--- before_pass
+++ after_pass
@@ -100,35 +100,17 @@ parser EgressParserImpl(packet_in buffer
     }
 }
 control ingress(inout headers hdr, inout metadata user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
-    psa_ingress_output_metadata_t meta_0;
-    PortId_t egress_port_0;
-    psa_ingress_output_metadata_t meta_1;
     @name("ingress.port_bytes_in") Counter<ByteCounter_t, PortId_t>(32w512, 32w1) port_bytes_in;
     @name("ingress.per_prefix_pkt_byte_count") DirectCounter<PacketByteCounter_t>(32w2) per_prefix_pkt_byte_count;
     @name("ingress.next_hop") action next_hop_0(PortId_t oport) {
         per_prefix_pkt_byte_count.count();
         {
             {
-                meta_0.class_of_service = ostd.class_of_service;
-                meta_0.clone = ostd.clone;
-                meta_0.clone_session_id = ostd.clone_session_id;
-                meta_0.drop = ostd.drop;
-                meta_0.resubmit = ostd.resubmit;
-                meta_0.multicast_group = ostd.multicast_group;
-                meta_0.egress_port = ostd.egress_port;
             }
-            egress_port_0 = oport;
-            meta_0.drop = false;
-            meta_0.multicast_group = 10w0;
-            meta_0.egress_port = egress_port_0;
             {
-                ostd.class_of_service = meta_0.class_of_service;
-                ostd.clone = meta_0.clone;
-                ostd.clone_session_id = meta_0.clone_session_id;
-                ostd.drop = meta_0.drop;
-                ostd.resubmit = meta_0.resubmit;
-                ostd.multicast_group = meta_0.multicast_group;
-                ostd.egress_port = meta_0.egress_port;
+                ostd.drop = false;
+                ostd.multicast_group = 10w0;
+                ostd.egress_port = oport;
             }
         }
     }
@@ -136,23 +118,9 @@ control ingress(inout headers hdr, inout
         per_prefix_pkt_byte_count.count();
         {
             {
-                meta_1.class_of_service = ostd.class_of_service;
-                meta_1.clone = ostd.clone;
-                meta_1.clone_session_id = ostd.clone_session_id;
-                meta_1.drop = ostd.drop;
-                meta_1.resubmit = ostd.resubmit;
-                meta_1.multicast_group = ostd.multicast_group;
-                meta_1.egress_port = ostd.egress_port;
             }
-            meta_1.drop = true;
             {
-                ostd.class_of_service = meta_1.class_of_service;
-                ostd.clone = meta_1.clone;
-                ostd.clone_session_id = meta_1.clone_session_id;
-                ostd.drop = meta_1.drop;
-                ostd.resubmit = meta_1.resubmit;
-                ostd.multicast_group = meta_1.multicast_group;
-                ostd.egress_port = meta_1.egress_port;
+                ostd.drop = true;
             }
         }
     }
