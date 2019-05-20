*** dumps/p4_16_samples/basic_routing-bmv2.p4/pruned/basic_routing-bmv2-BMV2::SimpleSwitchMidEnd_5_VisitFunctor.p4	2019-05-20 16:57:55.795624600 +0200
--- dumps/p4_16_samples/basic_routing-bmv2.p4/pruned/basic_routing-bmv2-BMV2::SimpleSwitchMidEnd_6_OrderArguments.p4	2019-05-20 16:57:55.798287200 +0200
*************** control DeparserImpl(packet_out packet,
*** 184,195 ****
  }
  control verifyChecksum(inout headers hdr, inout metadata meta) {
      apply {
!         verify_checksum<tuple<bit<4>, bit<4>, bit<8>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>, bit<16>>(data = { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, checksum = hdr.ipv4.hdrChecksum, condition = true, algo = HashAlgorithm.csum16);
      }
  }
  control computeChecksum(inout headers hdr, inout metadata meta) {
      apply {
!         update_checksum<tuple<bit<4>, bit<4>, bit<8>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>, bit<16>>(condition = true, data = { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, algo = HashAlgorithm.csum16, checksum = hdr.ipv4.hdrChecksum);
      }
  }
! V1Switch<headers, metadata>(p = ParserImpl(), ig = ingress(), vr = verifyChecksum(), eg = egress(), ck = computeChecksum(), dep = DeparserImpl()) main;
--- 184,195 ----
  }
  control verifyChecksum(inout headers hdr, inout metadata meta) {
      apply {
!         verify_checksum<tuple<bit<4>, bit<4>, bit<8>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>, bit<16>>(condition = true, data = { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, checksum = hdr.ipv4.hdrChecksum, algo = HashAlgorithm.csum16);
      }
  }
  control computeChecksum(inout headers hdr, inout metadata meta) {
      apply {
!         update_checksum<tuple<bit<4>, bit<4>, bit<8>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>, bit<16>>(condition = true, data = { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, checksum = hdr.ipv4.hdrChecksum, algo = HashAlgorithm.csum16);
      }
  }
! V1Switch<headers, metadata>(p = ParserImpl(), vr = verifyChecksum(), ig = ingress(), eg = egress(), ck = computeChecksum(), dep = DeparserImpl()) main;
