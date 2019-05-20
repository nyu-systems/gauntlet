*** dumps/p4_16_samples/psa-example-register2-bmv2.p4/pruned/psa-example-register2-bmv2-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-05-20 17:00:07.965788900 +0200
--- dumps/p4_16_samples/psa-example-register2-bmv2.p4/pruned/psa-example-register2-bmv2-BMV2::SimpleSwitchMidEnd_32_RemoveLeftSlices.p4	2019-05-20 17:00:07.971369500 +0200
*************** control ingress(inout headers hdr, inout
*** 51,58 ****
      PacketByteCountState_t s;
      @name(".update_pkt_ip_byte_count") action update_pkt_ip_byte_count() {
          s = tmp_1;
!         s[79:48] = tmp_1[79:48] + 32w1;
!         s[47:0] = s[47:0] + (bit<48>)hdr.ipv4.totalLen;
          tmp_1 = s;
      }
      @name("ingress.port_pkt_ip_bytes_in") Register<PacketByteCountState_t, PortId_t>(32w512) port_pkt_ip_bytes_in;
--- 51,58 ----
      PacketByteCountState_t s;
      @name(".update_pkt_ip_byte_count") action update_pkt_ip_byte_count() {
          s = tmp_1;
!         s = s & ~80w0xffffffff000000000000 | (bit<80>)(tmp_1[79:48] + 32w1) << 48 & 80w0xffffffff000000000000;
!         s = s & ~80w0xffffffffffff | (bit<80>)(s[47:0] + (bit<48>)hdr.ipv4.totalLen) << 0 & 80w0xffffffffffff;
          tmp_1 = s;
      }
      @name("ingress.port_pkt_ip_bytes_in") Register<PacketByteCountState_t, PortId_t>(32w512) port_pkt_ip_bytes_in;
