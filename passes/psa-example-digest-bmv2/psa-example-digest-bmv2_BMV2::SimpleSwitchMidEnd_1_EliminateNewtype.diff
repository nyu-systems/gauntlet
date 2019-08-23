--- before_pass
+++ after_pass
@@ -113,7 +113,7 @@ control ingress(inout headers hdr, inout
             psa_ingress_output_metadata_t meta_1 = ostd;
             PortId_t egress_port_1 = egress_port;
             meta_1.drop = false;
-            meta_1.multicast_group = (MulticastGroup_t)32w0;
+            meta_1.multicast_group = 32w0;
             meta_1.egress_port = egress_port_1;
             ostd = meta_1;
         }
@@ -123,7 +123,7 @@ control ingress(inout headers hdr, inout
             psa_ingress_output_metadata_t meta_2 = ostd;
             PortId_t egress_port_2 = egress_port;
             meta_2.drop = false;
-            meta_2.multicast_group = (MulticastGroup_t)32w0;
+            meta_2.multicast_group = 32w0;
             meta_2.egress_port = egress_port_2;
             ostd = meta_2;
         }
