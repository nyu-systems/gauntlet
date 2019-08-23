--- before_pass
+++ after_pass
@@ -56,19 +56,9 @@ struct headers {
     prot_i_t                 prot_inf_1;
 }
 parser PROTParser(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
-    bit<9> paddingLen_0;
-    bool currentISelected_0;
-    bit<8> hdrLeft_0;
-    bool currentISelected_1;
     prot_i_t inf_0;
-    bit<8> meta_0_headerLen;
-    bit<8> meta_0_hLeft;
-    bit<9> meta_0_addrLen;
     bit<8> meta_0_currPos;
     currenti_t meta_0_currenti;
-    bool currentISelected_2;
-    bit<8> currI_0;
-    bool subParser_currentISelected2;
     state start {
         packet.extract<preamble_t>(hdr.preamble);
         packet.extract<prot_common_t>(hdr.prot_common);
@@ -83,33 +73,22 @@ parser PROTParser(packet_in packet, out
     state parse_prot_host_addr_src_ipv4 {
         packet.extract<prot_host_addr_ipv4_t>(hdr.prot_host_addr_src.ipv4);
         meta._addrLen2 = meta._addrLen2 + 9w32;
-        paddingLen_0 = 9w64 - (meta._addrLen2 & 9w63) & 9w63;
-        packet.extract<prot_host_addr_padding_t>(hdr.prot_host_addr_padding, (bit<32>)paddingLen_0);
-        meta._addrLen2 = meta._addrLen2 + paddingLen_0;
+        packet.extract<prot_host_addr_padding_t>(hdr.prot_host_addr_padding, (bit<32>)(9w64 - (meta._addrLen2 & 9w63) & 9w63));
+        meta._addrLen2 = meta._addrLen2 + (9w64 - (meta._addrLen2 & 9w63) & 9w63);
         meta._currPos3 = (bit<8>)(9w3 + (meta._addrLen2 >> 6));
-        currentISelected_0 = hdr.prot_common.curri == meta._currPos3;
         inf_0.setInvalid();
         {
-            meta_0_headerLen = meta._headerLen0;
-            meta_0_hLeft = meta._hLeft1;
-            meta_0_addrLen = meta._addrLen2;
-            meta_0_currPos = meta._currPos3;
+            meta_0_currPos = (bit<8>)(9w3 + (meta._addrLen2 >> 6));
             {
                 meta_0_currenti.upDirection = meta._currenti_upDirection4;
             }
         }
-        currentISelected_2 = currentISelected_0;
-        currI_0 = hdr.prot_common.curri;
         packet.extract<prot_i_t>(inf_0);
-        subParser_currentISelected2 = currI_0 == meta_0_currPos;
-        meta_0_currenti.upDirection = meta_0_currenti.upDirection + (bit<1>)subParser_currentISelected2 * inf_0.upDirection;
-        meta_0_hLeft = inf_0.segLen;
-        meta_0_currPos = meta_0_currPos + 8w1;
+        meta_0_currenti.upDirection = meta._currenti_upDirection4 + (bit<1>)(hdr.prot_common.curri == (bit<8>)(9w3 + (meta._addrLen2 >> 6))) * inf_0.upDirection;
+        meta_0_currPos = (bit<8>)(9w3 + (meta._addrLen2 >> 6)) + 8w1;
         hdr.prot_inf_0 = inf_0;
         {
-            meta._headerLen0 = meta_0_headerLen;
-            meta._hLeft1 = meta_0_hLeft;
-            meta._addrLen2 = meta_0_addrLen;
+            meta._hLeft1 = inf_0.segLen;
             meta._currPos3 = meta_0_currPos;
             {
                 meta._currenti_upDirection4 = meta_0_currenti.upDirection;
@@ -130,37 +109,26 @@ parser PROTParser(packet_in packet, out
         transition parse_prot_h_0_pre;
     }
     state parse_prot_1 {
-        hdrLeft_0 = meta._headerLen0 - meta._currPos3;
-        transition select(hdrLeft_0) {
+        transition select(meta._headerLen0 - meta._currPos3) {
             8w0: accept;
             default: parse_prot_inf_1;
         }
     }
     state parse_prot_inf_1 {
-        currentISelected_1 = meta._currPos3 == hdr.prot_common.curri;
         inf_0.setInvalid();
         {
-            meta_0_headerLen = meta._headerLen0;
-            meta_0_hLeft = meta._hLeft1;
-            meta_0_addrLen = meta._addrLen2;
             meta_0_currPos = meta._currPos3;
             {
                 meta_0_currenti.upDirection = meta._currenti_upDirection4;
             }
         }
-        currentISelected_2 = currentISelected_1;
-        currI_0 = hdr.prot_common.curri;
         packet.extract<prot_i_t>(inf_0);
-        subParser_currentISelected2 = currI_0 == meta_0_currPos;
-        meta_0_currenti.upDirection = meta_0_currenti.upDirection + (bit<1>)subParser_currentISelected2 * inf_0.upDirection;
-        meta_0_hLeft = inf_0.segLen;
-        meta_0_currPos = meta_0_currPos + 8w1;
+        meta_0_currenti.upDirection = meta._currenti_upDirection4 + (bit<1>)(hdr.prot_common.curri == meta._currPos3) * inf_0.upDirection;
+        meta_0_currPos = meta._currPos3 + 8w1;
         hdr.prot_inf_1 = inf_0;
         {
-            meta._headerLen0 = meta_0_headerLen;
-            meta._hLeft1 = meta_0_hLeft;
-            meta._addrLen2 = meta_0_addrLen;
-            meta._currPos3 = meta_0_currPos;
+            meta._hLeft1 = inf_0.segLen;
+            meta._currPos3 = meta._currPos3 + 8w1;
             {
                 meta._currenti_upDirection4 = meta_0_currenti.upDirection;
             }
