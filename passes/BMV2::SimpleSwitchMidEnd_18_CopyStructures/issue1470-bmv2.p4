--- before_pass
+++ after_pass
@@ -41,7 +41,10 @@ parser OuterParser(packet_in pkt, out he
         transition start_0;
     }
     state start_0 {
-        hdr = hdr_1;
+        {
+            hdr.eth = hdr_1.eth;
+            hdr.ipv4 = hdr_1.ipv4;
+        }
         transition accept;
     }
 }
