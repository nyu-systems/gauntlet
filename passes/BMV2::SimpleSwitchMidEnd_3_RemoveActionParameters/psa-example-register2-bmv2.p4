--- before_pass
+++ after_pass
@@ -46,19 +46,24 @@ parser IngressParserImpl(packet_in buffe
     }
 }
 control ingress(inout headers hdr, inout metadata user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
-    @name(".update_pkt_ip_byte_count") action update_pkt_ip_byte_count(inout PacketByteCountState_t s, in bit<16> ip_length_bytes) {
+    PacketByteCountState_t tmp_1;
+    bit<80> tmp_2;
+    PacketByteCountState_t s;
+    bit<16> ip_length_bytes;
+    @name(".update_pkt_ip_byte_count") action update_pkt_ip_byte_count() {
+        s = tmp_1;
+        ip_length_bytes = hdr.ipv4.totalLen;
         s[79:48] = s[79:48] + 32w1;
         s[47:0] = s[47:0] + (bit<48>)ip_length_bytes;
+        tmp_1 = s;
     }
-    PacketByteCountState_t tmp_1;
-    bit<80> tmp_2;
     @name("ingress.port_pkt_ip_bytes_in") Register<PacketByteCountState_t, PortId_t>(32w512) port_pkt_ip_bytes_in;
     apply {
         ostd.egress_port = 10w0;
         if (hdr.ipv4.isValid()) @atomic {
             tmp_2 = port_pkt_ip_bytes_in.read(istd.ingress_port);
             tmp_1 = tmp_2;
-            update_pkt_ip_byte_count(tmp_1, hdr.ipv4.totalLen);
+            update_pkt_ip_byte_count();
             port_pkt_ip_bytes_in.write(istd.ingress_port, tmp_1);
         }
     }
