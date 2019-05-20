--- dumps/p4_16_samples/psa-example-digest-bmv2.p4/pruned/psa-example-digest-bmv2-BMV2::SimpleSwitchMidEnd_1_EliminateNewtype.p4	2019-05-20 17:31:44.966810000 +0200
+++ dumps/p4_16_samples/psa-example-digest-bmv2.p4/pruned/psa-example-digest-bmv2-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:31:44.832396100 +0200
@@ -1,14 +1,5 @@
 #include <core.p4>
 #include <psa.p4>
-enum bit<16> EthTypes {
-    IPv4 = 16w0x800,
-    ARP = 16w0x806,
-    RARP = 16w0x8035,
-    EtherTalk = 16w0x809b,
-    VLAN = 16w0x8100,
-    IPX = 16w0x8137,
-    IPv6 = 16w0x86dd
-}
 typedef bit<48> EthernetAddress;
 header ethernet_t {
     EthernetAddress dstAddr;
@@ -32,7 +23,7 @@ header ipv4_t {
 struct headers {
     ethernet_t ethernet;
     ipv4_t     ipv4;
-    EthTypes   type;
+    bit<16>    type;
 }
 struct empty_metadata_t {
 }
@@ -128,7 +119,7 @@ control ingress(inout headers hdr, inout
             ostd = meta_6;
         }
     }
-    @name("ingress.do_tst") action do_tst_0(PortId_t egress_port, EthTypes serEnumT) {
+    @name("ingress.do_tst") action do_tst_0(PortId_t egress_port, bit<16> serEnumT) {
         {
             psa_ingress_output_metadata_t meta_7 = ostd;
             PortId_t egress_port_3 = egress_port;
