--- before_pass
+++ after_pass
@@ -73,21 +73,13 @@ control ingress(inout headers hdr, inout
     @name("ingress.per_prefix_pkt_byte_count") DirectCounter<PacketByteCounter_t>(32w2) per_prefix_pkt_byte_count_0;
     @name("ingress.next_hop") action next_hop(PortId_t oport) {
         per_prefix_pkt_byte_count_0.count();
-        {
-            {
-                ostd.drop = false;
-                ostd.multicast_group = 32w0;
-                ostd.egress_port = oport;
-            }
-        }
+        ostd.drop = false;
+        ostd.multicast_group = 32w0;
+        ostd.egress_port = oport;
     }
     @name("ingress.default_route_drop") action default_route_drop() {
         per_prefix_pkt_byte_count_0.count();
-        {
-            {
-                ostd.drop = true;
-            }
-        }
+        ostd.drop = true;
     }
     @name("ingress.ipv4_da_lpm") table ipv4_da_lpm_0 {
         key = {
