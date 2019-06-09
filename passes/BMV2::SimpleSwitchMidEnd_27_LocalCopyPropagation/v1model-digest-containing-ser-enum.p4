--- before_pass
+++ after_pass
@@ -114,12 +114,12 @@ control MyIngress(inout headers hdr, ino
         meta._test_digest_in_mac_srcAddr0 = hdr.ethernet.srcAddr;
         meta._test_digest_my_parser_error1 = error.PacketTooShort;
         meta._test_digest_pkt_type2 = 32w0;
-        digest<test_digest_t>(32w1, {meta._test_digest_in_mac_srcAddr0,meta._test_digest_my_parser_error1,meta._test_digest_pkt_type2});
+        digest<test_digest_t>(32w1, {hdr.ethernet.srcAddr,error.PacketTooShort,32w0});
         meta._test_digest2_in_mac_dstAddr3 = hdr.ethernet.dstAddr;
         meta._test_digest2_my_thing4 = 8w42;
-        digest<test_digest2_t>(32w2, {meta._test_digest2_in_mac_dstAddr3,meta._test_digest2_my_thing4});
+        digest<test_digest2_t>(32w2, {hdr.ethernet.dstAddr,8w42});
         meta._test_digest3_in_mac_etherType5 = hdr.ethernet.etherType;
-        digest<test_digest3_t>(32w3, {meta._test_digest3_in_mac_etherType5});
+        digest<test_digest3_t>(32w3, {hdr.ethernet.etherType});
     }
     apply {
         ipv4_lpm_0.apply();
