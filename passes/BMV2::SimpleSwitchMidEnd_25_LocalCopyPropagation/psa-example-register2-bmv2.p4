--- dumps/p4_16_samples/psa-example-register2-bmv2.p4/pruned/psa-example-register2-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:31:46.033050700 +0200
+++ dumps/p4_16_samples/psa-example-register2-bmv2.p4/pruned/psa-example-register2-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:31:46.035540200 +0200
@@ -49,12 +49,10 @@ control ingress(inout headers hdr, inout
     PacketByteCountState_t tmp_1;
     bit<80> tmp_2;
     PacketByteCountState_t s;
-    bit<16> ip_length_bytes;
     @name(".update_pkt_ip_byte_count") action update_pkt_ip_byte_count() {
         s = tmp_1;
-        ip_length_bytes = hdr.ipv4.totalLen;
-        s[79:48] = s[79:48] + 32w1;
-        s[47:0] = s[47:0] + (bit<48>)ip_length_bytes;
+        s[79:48] = tmp_1[79:48] + 32w1;
+        s[47:0] = s[47:0] + (bit<48>)hdr.ipv4.totalLen;
         tmp_1 = s;
     }
     @name("ingress.port_pkt_ip_bytes_in") Register<PacketByteCountState_t, PortId_t>(32w512) port_pkt_ip_bytes_in;
