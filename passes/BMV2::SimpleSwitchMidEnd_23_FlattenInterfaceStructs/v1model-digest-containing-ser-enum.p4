--- before_pass
+++ after_pass
@@ -42,9 +42,12 @@ struct test_digest3_t {
     bit<16> in_mac_etherType;
 }
 struct metadata {
-    test_digest_t  test_digest;
-    test_digest2_t test_digest2;
-    test_digest3_t test_digest3;
+    bit<48> _test_digest_in_mac_srcAddr0;
+    error   _test_digest_my_parser_error1;
+    bit<32> _test_digest_pkt_type2;
+    bit<48> _test_digest2_in_mac_dstAddr3;
+    bit<8>  _test_digest2_my_thing4;
+    bit<16> _test_digest3_in_mac_etherType5;
 }
 struct headers {
     ethernet_t ethernet;
@@ -108,15 +111,15 @@ control MyIngress(inout headers hdr, ino
         default_action = NoAction_1();
     }
     @name("MyIngress.send_digest") action send_digest() {
-        meta.test_digest.in_mac_srcAddr = hdr.ethernet.srcAddr;
-        meta.test_digest.my_parser_error = error.PacketTooShort;
-        meta.test_digest.pkt_type = 32w0;
-        digest<test_digest_t>(32w1, meta.test_digest);
-        meta.test_digest2.in_mac_dstAddr = hdr.ethernet.dstAddr;
-        meta.test_digest2.my_thing = 8w42;
-        digest<test_digest2_t>(32w2, meta.test_digest2);
-        meta.test_digest3.in_mac_etherType = hdr.ethernet.etherType;
-        digest<test_digest3_t>(32w3, meta.test_digest3);
+        meta._test_digest_in_mac_srcAddr0 = hdr.ethernet.srcAddr;
+        meta._test_digest_my_parser_error1 = error.PacketTooShort;
+        meta._test_digest_pkt_type2 = 32w0;
+        digest<test_digest_t>(32w1, {meta._test_digest_in_mac_srcAddr0,meta._test_digest_my_parser_error1,meta._test_digest_pkt_type2});
+        meta._test_digest2_in_mac_dstAddr3 = hdr.ethernet.dstAddr;
+        meta._test_digest2_my_thing4 = 8w42;
+        digest<test_digest2_t>(32w2, {meta._test_digest2_in_mac_dstAddr3,meta._test_digest2_my_thing4});
+        meta._test_digest3_in_mac_etherType5 = hdr.ethernet.etherType;
+        digest<test_digest3_t>(32w3, {meta._test_digest3_in_mac_etherType5});
     }
     apply {
         ipv4_lpm_0.apply();
