--- before_pass
+++ after_pass
@@ -114,12 +114,12 @@ control MyIngress(inout headers hdr, ino
         meta._test_digest_in_mac_srcAddr0 = hdr.ethernet.srcAddr;
         meta._test_digest_my_parser_error1 = error.PacketTooShort;
         meta._test_digest_pkt_type2 = 32w0;
-        digest<test_digest_t>(32w1, test_digest_t {in_mac_srcAddr = meta._test_digest_in_mac_srcAddr0,my_parser_error = meta._test_digest_my_parser_error1,pkt_type = meta._test_digest_pkt_type2});
+        digest<test_digest_t>(32w1, test_digest_t {in_mac_srcAddr = hdr.ethernet.srcAddr,my_parser_error = error.PacketTooShort,pkt_type = 32w0});
         meta._test_digest2_in_mac_dstAddr3 = hdr.ethernet.dstAddr;
         meta._test_digest2_my_thing4 = 8w42;
-        digest<test_digest2_t>(32w2, test_digest2_t {in_mac_dstAddr = meta._test_digest2_in_mac_dstAddr3,my_thing = meta._test_digest2_my_thing4});
+        digest<test_digest2_t>(32w2, test_digest2_t {in_mac_dstAddr = hdr.ethernet.dstAddr,my_thing = 8w42});
         meta._test_digest3_in_mac_etherType5 = hdr.ethernet.etherType;
-        digest<test_digest3_t>(32w3, test_digest3_t {in_mac_etherType = meta._test_digest3_in_mac_etherType5});
+        digest<test_digest3_t>(32w3, test_digest3_t {in_mac_etherType = hdr.ethernet.etherType});
     }
     apply {
         ipv4_lpm_0.apply();
