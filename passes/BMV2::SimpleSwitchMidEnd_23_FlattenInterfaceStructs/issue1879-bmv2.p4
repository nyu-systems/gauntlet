--- before_pass
+++ after_pass
@@ -38,11 +38,11 @@ struct currenti_t {
     bit<1> upDirection;
 }
 struct metadata {
-    bit<8>     headerLen;
-    bit<8>     hLeft;
-    bit<9>     addrLen;
-    bit<8>     currPos;
-    currenti_t currenti;
+    bit<8> _headerLen0;
+    bit<8> _hLeft1;
+    bit<9> _addrLen2;
+    bit<8> _currPos3;
+    bit<1> _currenti_upDirection4;
 }
 struct headers {
     preamble_t               preamble;
@@ -73,29 +73,29 @@ parser PROTParser(packet_in packet, out
         packet.extract<preamble_t>(hdr.preamble);
         packet.extract<prot_common_t>(hdr.prot_common);
         packet.extract<prot_addr_common_t>(hdr.prot_addr_common);
-        meta.headerLen = hdr.prot_common.hdrLen;
+        meta._headerLen0 = hdr.prot_common.hdrLen;
         packet.extract<prot_host_addr_ipv4_t>(hdr.prot_host_addr_dst.ipv4);
-        meta.addrLen = 9w32;
+        meta._addrLen2 = 9w32;
         transition select(hdr.prot_common.srcType) {
             6w0x1: parse_prot_host_addr_src_ipv4;
         }
     }
     state parse_prot_host_addr_src_ipv4 {
         packet.extract<prot_host_addr_ipv4_t>(hdr.prot_host_addr_src.ipv4);
-        meta.addrLen = meta.addrLen + 9w32;
-        paddingLen_0 = 9w64 - (meta.addrLen & 9w63) & 9w63;
+        meta._addrLen2 = meta._addrLen2 + 9w32;
+        paddingLen_0 = 9w64 - (meta._addrLen2 & 9w63) & 9w63;
         packet.extract<prot_host_addr_padding_t>(hdr.prot_host_addr_padding, (bit<32>)paddingLen_0);
-        meta.addrLen = meta.addrLen + paddingLen_0;
-        meta.currPos = (bit<8>)(9w3 + (meta.addrLen >> 6));
-        currentISelected_0 = hdr.prot_common.curri == meta.currPos;
+        meta._addrLen2 = meta._addrLen2 + paddingLen_0;
+        meta._currPos3 = (bit<8>)(9w3 + (meta._addrLen2 >> 6));
+        currentISelected_0 = hdr.prot_common.curri == meta._currPos3;
         inf_0.setInvalid();
         {
-            meta_0_headerLen = meta.headerLen;
-            meta_0_hLeft = meta.hLeft;
-            meta_0_addrLen = meta.addrLen;
-            meta_0_currPos = meta.currPos;
+            meta_0_headerLen = meta._headerLen0;
+            meta_0_hLeft = meta._hLeft1;
+            meta_0_addrLen = meta._addrLen2;
+            meta_0_currPos = meta._currPos3;
             {
-                meta_0_currenti.upDirection = meta.currenti.upDirection;
+                meta_0_currenti.upDirection = meta._currenti_upDirection4;
             }
         }
         currentISelected_2 = currentISelected_0;
@@ -107,45 +107,45 @@ parser PROTParser(packet_in packet, out
         meta_0_currPos = meta_0_currPos + 8w1;
         hdr.prot_inf_0 = inf_0;
         {
-            meta.headerLen = meta_0_headerLen;
-            meta.hLeft = meta_0_hLeft;
-            meta.addrLen = meta_0_addrLen;
-            meta.currPos = meta_0_currPos;
+            meta._headerLen0 = meta_0_headerLen;
+            meta._hLeft1 = meta_0_hLeft;
+            meta._addrLen2 = meta_0_addrLen;
+            meta._currPos3 = meta_0_currPos;
             {
-                meta.currenti.upDirection = meta_0_currenti.upDirection;
+                meta._currenti_upDirection4 = meta_0_currenti.upDirection;
             }
         }
         transition parse_prot_h_0_pre;
     }
     state parse_prot_h_0_pre {
-        transition select(meta.hLeft) {
+        transition select(meta._hLeft1) {
             8w0: parse_prot_1;
             default: parse_prot_h_0;
         }
     }
     state parse_prot_h_0 {
         packet.extract<prot_h_t>(hdr.prot_h_0.next);
-        meta.hLeft = meta.hLeft + 8w255;
-        meta.currPos = meta.currPos + 8w1;
+        meta._hLeft1 = meta._hLeft1 + 8w255;
+        meta._currPos3 = meta._currPos3 + 8w1;
         transition parse_prot_h_0_pre;
     }
     state parse_prot_1 {
-        hdrLeft_0 = meta.headerLen - meta.currPos;
+        hdrLeft_0 = meta._headerLen0 - meta._currPos3;
         transition select(hdrLeft_0) {
             8w0: accept;
             default: parse_prot_inf_1;
         }
     }
     state parse_prot_inf_1 {
-        currentISelected_1 = meta.currPos == hdr.prot_common.curri;
+        currentISelected_1 = meta._currPos3 == hdr.prot_common.curri;
         inf_0.setInvalid();
         {
-            meta_0_headerLen = meta.headerLen;
-            meta_0_hLeft = meta.hLeft;
-            meta_0_addrLen = meta.addrLen;
-            meta_0_currPos = meta.currPos;
+            meta_0_headerLen = meta._headerLen0;
+            meta_0_hLeft = meta._hLeft1;
+            meta_0_addrLen = meta._addrLen2;
+            meta_0_currPos = meta._currPos3;
             {
-                meta_0_currenti.upDirection = meta.currenti.upDirection;
+                meta_0_currenti.upDirection = meta._currenti_upDirection4;
             }
         }
         currentISelected_2 = currentISelected_1;
@@ -157,12 +157,12 @@ parser PROTParser(packet_in packet, out
         meta_0_currPos = meta_0_currPos + 8w1;
         hdr.prot_inf_1 = inf_0;
         {
-            meta.headerLen = meta_0_headerLen;
-            meta.hLeft = meta_0_hLeft;
-            meta.addrLen = meta_0_addrLen;
-            meta.currPos = meta_0_currPos;
+            meta._headerLen0 = meta_0_headerLen;
+            meta._hLeft1 = meta_0_hLeft;
+            meta._addrLen2 = meta_0_addrLen;
+            meta._currPos3 = meta_0_currPos;
             {
-                meta.currenti.upDirection = meta_0_currenti.upDirection;
+                meta._currenti_upDirection4 = meta_0_currenti.upDirection;
             }
         }
         transition accept;
@@ -174,7 +174,7 @@ control PROTVerifyChecksum(inout headers
 }
 control PROTIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
     apply {
-        if (meta.currenti.upDirection == 1w0) 
+        if (meta._currenti_upDirection4 == 1w0) 
             mark_to_drop(standard_metadata);
     }
 }
