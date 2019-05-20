*** dumps/p4_16_samples/v1model-digest-containing-ser-enum.p4/pruned/v1model-digest-containing-ser-enum-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 17:00:45.035154400 +0200
--- dumps/p4_16_samples/v1model-digest-containing-ser-enum.p4/pruned/v1model-digest-containing-ser-enum-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:00:45.040260700 +0200
*************** control MyEgress(inout headers hdr, inou
*** 142,150 ****
          send_frame.apply();
      }
  }
  control MyComputeChecksum(inout headers hdr, inout metadata meta) {
      apply {
!         update_checksum<tuple<bit<4>, bit<4>, bit<8>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>, bit<16>>(hdr.ipv4.isValid(), { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
      }
  }
  control MyDeparser(packet_out packet, in headers hdr) {
--- 142,163 ----
          send_frame.apply();
      }
  }
+ struct tuple_0 {
+     bit<4>  field;
+     bit<4>  field_0;
+     bit<8>  field_1;
+     bit<16> field_2;
+     bit<16> field_3;
+     bit<3>  field_4;
+     bit<13> field_5;
+     bit<8>  field_6;
+     bit<8>  field_7;
+     bit<32> field_8;
+     bit<32> field_9;
+ }
  control MyComputeChecksum(inout headers hdr, inout metadata meta) {
      apply {
!         update_checksum<tuple_0, bit<16>>(hdr.ipv4.isValid(), { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
      }
  }
  control MyDeparser(packet_out packet, in headers hdr) {
