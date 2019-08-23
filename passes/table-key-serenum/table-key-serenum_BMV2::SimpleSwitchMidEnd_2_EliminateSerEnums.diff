--- before_pass
+++ after_pass
@@ -1,18 +1,9 @@
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
 header Ethernet {
-    bit<48>  src;
-    bit<48>  dest;
-    EthTypes type;
+    bit<48> src;
+    bit<48> dest;
+    bit<16> type;
 }
 struct Headers {
     Ethernet eth;
@@ -22,8 +13,8 @@ parser prs(packet_in p, out Headers h) {
     state start {
         p.extract<Ethernet>(e_0);
         transition select(e_0.type) {
-            EthTypes.IPv4: accept;
-            EthTypes.ARP: accept;
+            16w0x800: accept;
+            16w0x806: accept;
             default: reject;
         }
     }
@@ -43,8 +34,8 @@ control c(inout Headers h, inout standar
             @defaultonly NoAction_0();
         }
         const entries = {
-                        EthTypes.IPv4 : do_act(32w0x800);
-                        EthTypes.VLAN : do_act(32w0x8100);
+                        16w0x800 : do_act(32w0x800);
+                        16w0x8100 : do_act(32w0x8100);
         }
         default_action = NoAction_0();
     }
