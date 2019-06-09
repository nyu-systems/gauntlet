--- before_pass
+++ after_pass
@@ -85,7 +85,15 @@ parser PROTParser(packet_in packet, out
         meta.currPos = (bit<8>)(9w3 + (meta.addrLen >> 6));
         currentISelected_0 = hdr.prot_common.curri == meta.currPos;
         inf_0.setInvalid();
-        meta_0 = meta;
+        {
+            meta_0.headerLen = meta.headerLen;
+            meta_0.hLeft = meta.hLeft;
+            meta_0.addrLen = meta.addrLen;
+            meta_0.currPos = meta.currPos;
+            {
+                meta_0.currenti.upDirection = meta.currenti.upDirection;
+            }
+        }
         currentISelected_2 = currentISelected_0;
         currI_0 = hdr.prot_common.curri;
         packet.extract<prot_i_t>(inf_0);
@@ -94,7 +102,15 @@ parser PROTParser(packet_in packet, out
         meta_0.hLeft = inf_0.segLen;
         meta_0.currPos = meta_0.currPos + 8w1;
         hdr.prot_inf_0 = inf_0;
-        meta = meta_0;
+        {
+            meta.headerLen = meta_0.headerLen;
+            meta.hLeft = meta_0.hLeft;
+            meta.addrLen = meta_0.addrLen;
+            meta.currPos = meta_0.currPos;
+            {
+                meta.currenti.upDirection = meta_0.currenti.upDirection;
+            }
+        }
         transition parse_prot_h_0_pre;
     }
     state parse_prot_h_0_pre {
@@ -119,7 +135,15 @@ parser PROTParser(packet_in packet, out
     state parse_prot_inf_1 {
         currentISelected_1 = meta.currPos == hdr.prot_common.curri;
         inf_0.setInvalid();
-        meta_0 = meta;
+        {
+            meta_0.headerLen = meta.headerLen;
+            meta_0.hLeft = meta.hLeft;
+            meta_0.addrLen = meta.addrLen;
+            meta_0.currPos = meta.currPos;
+            {
+                meta_0.currenti.upDirection = meta.currenti.upDirection;
+            }
+        }
         currentISelected_2 = currentISelected_1;
         currI_0 = hdr.prot_common.curri;
         packet.extract<prot_i_t>(inf_0);
@@ -128,7 +152,15 @@ parser PROTParser(packet_in packet, out
         meta_0.hLeft = inf_0.segLen;
         meta_0.currPos = meta_0.currPos + 8w1;
         hdr.prot_inf_1 = inf_0;
-        meta = meta_0;
+        {
+            meta.headerLen = meta_0.headerLen;
+            meta.hLeft = meta_0.hLeft;
+            meta.addrLen = meta_0.addrLen;
+            meta.currPos = meta_0.currPos;
+            {
+                meta.currenti.upDirection = meta_0.currenti.upDirection;
+            }
+        }
         transition accept;
     }
 }
