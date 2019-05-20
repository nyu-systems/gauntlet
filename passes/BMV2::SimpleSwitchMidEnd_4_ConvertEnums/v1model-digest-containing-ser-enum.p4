*** dumps/p4_16_samples/v1model-digest-containing-ser-enum.p4/pruned/v1model-digest-containing-ser-enum-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:00:45.144760800 +0200
--- dumps/p4_16_samples/v1model-digest-containing-ser-enum.p4/pruned/v1model-digest-containing-ser-enum-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-05-20 17:00:45.044713700 +0200
*************** header ipv4_t {
*** 25,38 ****
      ip4Addr_t srcAddr;
      ip4Addr_t dstAddr;
  }
- enum MyPacketTypes {
-     IPv4,
-     Other
- }
  struct test_digest_t {
!     macAddr_t     in_mac_srcAddr;
!     error         my_parser_error;
!     MyPacketTypes pkt_type;
  }
  struct test_digest2_t {
      macAddr_t in_mac_dstAddr;
--- 25,34 ----
      ip4Addr_t srcAddr;
      ip4Addr_t dstAddr;
  }
  struct test_digest_t {
!     macAddr_t in_mac_srcAddr;
!     error     my_parser_error;
!     bit<32>   pkt_type;
  }
  struct test_digest2_t {
      macAddr_t in_mac_dstAddr;
*************** control MyIngress(inout headers hdr, ino
*** 110,116 ****
      @name("MyIngress.send_digest") action send_digest_0() {
          meta.test_digest.in_mac_srcAddr = hdr.ethernet.srcAddr;
          meta.test_digest.my_parser_error = error.PacketTooShort;
!         meta.test_digest.pkt_type = MyPacketTypes.IPv4;
          digest<test_digest_t>(32w1, meta.test_digest);
          meta.test_digest2.in_mac_dstAddr = hdr.ethernet.dstAddr;
          meta.test_digest2.my_thing = 8w42;
--- 106,112 ----
      @name("MyIngress.send_digest") action send_digest_0() {
          meta.test_digest.in_mac_srcAddr = hdr.ethernet.srcAddr;
          meta.test_digest.my_parser_error = error.PacketTooShort;
!         meta.test_digest.pkt_type = 32w0;
          digest<test_digest_t>(32w1, meta.test_digest);
          meta.test_digest2.in_mac_dstAddr = hdr.ethernet.dstAddr;
          meta.test_digest2.my_thing = 8w42;
