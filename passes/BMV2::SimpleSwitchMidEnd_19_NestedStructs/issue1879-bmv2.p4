--- before_pass
+++ after_pass
@@ -61,7 +61,11 @@ parser PROTParser(packet_in packet, out
     bit<8> hdrLeft_0;
     bool currentISelected_1;
     prot_i_t inf_0;
-    metadata meta_0;
+    bit<8> meta_0_headerLen;
+    bit<8> meta_0_hLeft;
+    bit<9> meta_0_addrLen;
+    bit<8> meta_0_currPos;
+    currenti_t meta_0_currenti;
     bool currentISelected_2;
     bit<8> currI_0;
     bool subParser_currentISelected2;
@@ -86,29 +90,29 @@ parser PROTParser(packet_in packet, out
         currentISelected_0 = hdr.prot_common.curri == meta.currPos;
         inf_0.setInvalid();
         {
-            meta_0.headerLen = meta.headerLen;
-            meta_0.hLeft = meta.hLeft;
-            meta_0.addrLen = meta.addrLen;
-            meta_0.currPos = meta.currPos;
+            meta_0_headerLen = meta.headerLen;
+            meta_0_hLeft = meta.hLeft;
+            meta_0_addrLen = meta.addrLen;
+            meta_0_currPos = meta.currPos;
             {
-                meta_0.currenti.upDirection = meta.currenti.upDirection;
+                meta_0_currenti.upDirection = meta.currenti.upDirection;
             }
         }
         currentISelected_2 = currentISelected_0;
         currI_0 = hdr.prot_common.curri;
         packet.extract<prot_i_t>(inf_0);
-        subParser_currentISelected2 = currI_0 == meta_0.currPos;
-        meta_0.currenti.upDirection = meta_0.currenti.upDirection + (bit<1>)subParser_currentISelected2 * inf_0.upDirection;
-        meta_0.hLeft = inf_0.segLen;
-        meta_0.currPos = meta_0.currPos + 8w1;
+        subParser_currentISelected2 = currI_0 == meta_0_currPos;
+        meta_0_currenti.upDirection = meta_0_currenti.upDirection + (bit<1>)subParser_currentISelected2 * inf_0.upDirection;
+        meta_0_hLeft = inf_0.segLen;
+        meta_0_currPos = meta_0_currPos + 8w1;
         hdr.prot_inf_0 = inf_0;
         {
-            meta.headerLen = meta_0.headerLen;
-            meta.hLeft = meta_0.hLeft;
-            meta.addrLen = meta_0.addrLen;
-            meta.currPos = meta_0.currPos;
+            meta.headerLen = meta_0_headerLen;
+            meta.hLeft = meta_0_hLeft;
+            meta.addrLen = meta_0_addrLen;
+            meta.currPos = meta_0_currPos;
             {
-                meta.currenti.upDirection = meta_0.currenti.upDirection;
+                meta.currenti.upDirection = meta_0_currenti.upDirection;
             }
         }
         transition parse_prot_h_0_pre;
@@ -136,29 +140,29 @@ parser PROTParser(packet_in packet, out
         currentISelected_1 = meta.currPos == hdr.prot_common.curri;
         inf_0.setInvalid();
         {
-            meta_0.headerLen = meta.headerLen;
-            meta_0.hLeft = meta.hLeft;
-            meta_0.addrLen = meta.addrLen;
-            meta_0.currPos = meta.currPos;
+            meta_0_headerLen = meta.headerLen;
+            meta_0_hLeft = meta.hLeft;
+            meta_0_addrLen = meta.addrLen;
+            meta_0_currPos = meta.currPos;
             {
-                meta_0.currenti.upDirection = meta.currenti.upDirection;
+                meta_0_currenti.upDirection = meta.currenti.upDirection;
             }
         }
         currentISelected_2 = currentISelected_1;
         currI_0 = hdr.prot_common.curri;
         packet.extract<prot_i_t>(inf_0);
-        subParser_currentISelected2 = currI_0 == meta_0.currPos;
-        meta_0.currenti.upDirection = meta_0.currenti.upDirection + (bit<1>)subParser_currentISelected2 * inf_0.upDirection;
-        meta_0.hLeft = inf_0.segLen;
-        meta_0.currPos = meta_0.currPos + 8w1;
+        subParser_currentISelected2 = currI_0 == meta_0_currPos;
+        meta_0_currenti.upDirection = meta_0_currenti.upDirection + (bit<1>)subParser_currentISelected2 * inf_0.upDirection;
+        meta_0_hLeft = inf_0.segLen;
+        meta_0_currPos = meta_0_currPos + 8w1;
         hdr.prot_inf_1 = inf_0;
         {
-            meta.headerLen = meta_0.headerLen;
-            meta.hLeft = meta_0.hLeft;
-            meta.addrLen = meta_0.addrLen;
-            meta.currPos = meta_0.currPos;
+            meta.headerLen = meta_0_headerLen;
+            meta.hLeft = meta_0_hLeft;
+            meta.addrLen = meta_0_addrLen;
+            meta.currPos = meta_0_currPos;
             {
-                meta.currenti.upDirection = meta_0.currenti.upDirection;
+                meta.currenti.upDirection = meta_0_currenti.upDirection;
             }
         }
         transition accept;
