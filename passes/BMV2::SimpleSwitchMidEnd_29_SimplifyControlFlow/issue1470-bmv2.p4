--- before_pass
+++ after_pass
@@ -42,10 +42,8 @@ parser OuterParser(packet_in pkt, out he
         transition start_0;
     }
     state start_0 {
-        {
-            hdr.eth = hdr_1_eth;
-            hdr.ipv4 = hdr_1_ipv4;
-        }
+        hdr.eth = hdr_1_eth;
+        hdr.ipv4 = hdr_1_ipv4;
         transition accept;
     }
 }
