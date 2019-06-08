--- before_pass
+++ after_pass
@@ -1,17 +1,8 @@
 #include <core.p4>
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
@@ -21,8 +12,8 @@ parser prs(packet_in p, out Headers h) {
     state start {
         p.extract<Ethernet>(e);
         transition select(e.type) {
-            EthTypes.IPv4: accept;
-            EthTypes.ARP: accept;
+            16w0x800: accept;
+            16w0x806: accept;
             default: reject;
         }
     }
@@ -33,10 +24,10 @@ control c(inout Headers h) {
         if (!h.eth.isValid()) 
             hasReturned_0 = true;
         if (!hasReturned_0) 
-            if (h.eth.type == EthTypes.IPv4) 
+            if (h.eth.type == 16w0x800) 
                 h.eth.setInvalid();
             else 
-                h.eth.type = (EthTypes)16w0;
+                h.eth.type = (bit<16>)16w0;
     }
 }
 parser p<H>(packet_in _p, out H h);
