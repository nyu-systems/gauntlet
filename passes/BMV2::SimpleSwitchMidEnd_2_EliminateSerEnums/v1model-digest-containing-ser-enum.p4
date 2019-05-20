--- dumps/p4_16_samples/v1model-digest-containing-ser-enum.p4/pruned/v1model-digest-containing-ser-enum-BMV2::SimpleSwitchMidEnd_1_EliminateNewtype.p4	2019-05-20 17:32:24.415654000 +0200
+++ dumps/p4_16_samples/v1model-digest-containing-ser-enum.p4/pruned/v1model-digest-containing-ser-enum-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:32:24.451919300 +0200
@@ -29,19 +29,14 @@ enum MyPacketTypes {
     IPv4,
     Other
 }
-enum bit<8> MySerEnum1 {
-    foo = 8w28,
-    bar = 8w17,
-    gah = 8w42
-}
 struct test_digest_t {
     macAddr_t     in_mac_srcAddr;
     error         my_parser_error;
     MyPacketTypes pkt_type;
 }
 struct test_digest2_t {
-    macAddr_t  in_mac_dstAddr;
-    MySerEnum1 my_thing;
+    macAddr_t in_mac_dstAddr;
+    bit<8>    my_thing;
 }
 struct test_digest3_t {
     bit<16> in_mac_etherType;
@@ -118,7 +113,7 @@ control MyIngress(inout headers hdr, ino
         meta.test_digest.pkt_type = MyPacketTypes.IPv4;
         digest<test_digest_t>(32w1, meta.test_digest);
         meta.test_digest2.in_mac_dstAddr = hdr.ethernet.dstAddr;
-        meta.test_digest2.my_thing = MySerEnum1.gah;
+        meta.test_digest2.my_thing = 8w42;
         digest<test_digest2_t>(32w2, meta.test_digest2);
         meta.test_digest3.in_mac_etherType = hdr.ethernet.etherType;
         digest<test_digest3_t>(32w3, meta.test_digest3);
