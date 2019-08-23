--- before_pass
+++ after_pass
@@ -84,7 +84,7 @@ control ingress(inout headers hdr, inout
             psa_ingress_output_metadata_t meta_2 = ostd;
             PortId_t egress_port_1 = oport;
             meta_2.drop = false;
-            meta_2.multicast_group = (MulticastGroup_t)32w0;
+            meta_2.multicast_group = 32w0;
             meta_2.egress_port = egress_port_1;
             ostd = meta_2;
         }
