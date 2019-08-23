--- before_pass
+++ after_pass
@@ -54,7 +54,7 @@ control ingress(inout headers hdr, inout
     bit<80> tmp_0;
     @name("ingress.port_pkt_ip_bytes_in") Register<PacketByteCountState_t, PortId_t>(32w512) port_pkt_ip_bytes_in_0;
     apply {
-        ostd.egress_port = (PortId_t)32w0;
+        ostd.egress_port = 32w0;
         if (hdr.ipv4.isValid()) @atomic {
             tmp_0 = port_pkt_ip_bytes_in_0.read(istd.ingress_port);
             tmp = tmp_0;
