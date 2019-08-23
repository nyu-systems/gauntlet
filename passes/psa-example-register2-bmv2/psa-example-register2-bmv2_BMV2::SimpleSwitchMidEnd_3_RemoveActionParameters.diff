--- before_pass
+++ after_pass
@@ -46,19 +46,24 @@ parser IngressParserImpl(packet_in buffe
     }
 }
 control ingress(inout headers hdr, inout metadata user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
-    @name(".update_pkt_ip_byte_count") action update_pkt_ip_byte_count(inout PacketByteCountState_t s, in bit<16> ip_length_bytes) {
+    PacketByteCountState_t tmp;
+    bit<80> tmp_0;
+    PacketByteCountState_t s;
+    bit<16> ip_length_bytes;
+    @name(".update_pkt_ip_byte_count") action update_pkt_ip_byte_count() {
+        s = tmp;
+        ip_length_bytes = hdr.ipv4.totalLen;
         s[79:48] = s[79:48] + 32w1;
         s[47:0] = s[47:0] + (bit<48>)ip_length_bytes;
+        tmp = s;
     }
-    PacketByteCountState_t tmp;
-    bit<80> tmp_0;
     @name("ingress.port_pkt_ip_bytes_in") Register<PacketByteCountState_t, PortId_t>(32w512) port_pkt_ip_bytes_in_0;
     apply {
         ostd.egress_port = 32w0;
         if (hdr.ipv4.isValid()) @atomic {
             tmp_0 = port_pkt_ip_bytes_in_0.read(istd.ingress_port);
             tmp = tmp_0;
-            update_pkt_ip_byte_count(tmp, hdr.ipv4.totalLen);
+            update_pkt_ip_byte_count();
             port_pkt_ip_bytes_in_0.write(istd.ingress_port, tmp);
         }
     }
