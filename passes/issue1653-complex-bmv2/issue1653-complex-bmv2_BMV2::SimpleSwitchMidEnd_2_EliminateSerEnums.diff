--- before_pass
+++ after_pass
@@ -1,21 +1,12 @@
 #include <core.p4>
 #include <v1model.p4>
-enum bit<16> EthTypes {
-    IPv4 = 16w0x800,
-    ARP = 16w0x806,
-    RARP = 16w0x8035,
-    EtherTalk = 16w0x809b,
-    VLAN = 16w0x8100,
-    IPX = 16w0x8137,
-    IPv6 = 16w0x86dd
-}
 struct alt_t {
-    bit<1>   valid;
-    bit<7>   port;
-    int<8>   hashRes;
-    bool     useHash;
-    EthTypes type;
-    bit<7>   pad;
+    bit<1>  valid;
+    bit<7>  port;
+    int<8>  hashRes;
+    bool    useHash;
+    bit<16> type;
+    bit<7>  pad;
 }
 struct row_t {
     alt_t alt0;
@@ -62,7 +53,7 @@ control ingress(inout parsed_packet_t h,
     }
     apply {
         tns_0.apply();
-        bh_0.row.alt1.type = EthTypes.IPv4;
+        bh_0.row.alt1.type = 16w0x800;
         h.bvh0.row.alt1.type = bh_0.row.alt1.type;
         local_metadata.row0.alt0.useHash = true;
         clone3<row_t>(CloneType.I2E, 32w0, local_metadata.row0);
