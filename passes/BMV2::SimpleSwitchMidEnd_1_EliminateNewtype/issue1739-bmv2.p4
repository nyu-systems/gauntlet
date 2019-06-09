--- before_pass
+++ after_pass
@@ -1,10 +1,10 @@
 #include <core.p4>
 #include <v1model.p4>
 typedef bit<48> EthernetAddressUint_t;
-type EthernetAddressUint_t EthernetAddress_t;
+typedef EthernetAddressUint_t EthernetAddress_t;
 typedef bit<32> IPv4AddressUint_t;
-type IPv4AddressUint_t IPv4Address_t;
-type IPv4Address_t IPv4Address2_t;
+typedef IPv4AddressUint_t IPv4Address_t;
+typedef IPv4Address_t IPv4Address2_t;
 header ethernet_t {
     EthernetAddress_t dstAddr;
     EthernetAddress_t srcAddr;
