--- before_pass
+++ after_pass
@@ -43,7 +43,10 @@ parser ProtParser(packet_in packet, out
         transition start_0;
     }
     state start_0 {
-        hdr.addr_dst = addr_1;
+        {
+            hdr.addr_dst.ipv4 = addr_1.ipv4;
+            hdr.addr_dst.ipv6 = addr_1.ipv6;
+        }
         addrType = hdr.addr_type.srcType;
         addr_1.ipv4.setInvalid();
         addr_1.ipv6.setInvalid();
@@ -61,7 +64,10 @@ parser ProtParser(packet_in packet, out
         transition start_1;
     }
     state start_1 {
-        hdr.addr_src = addr_1;
+        {
+            hdr.addr_src.ipv4 = addr_1.ipv4;
+            hdr.addr_src.ipv6 = addr_1.ipv6;
+        }
         transition accept;
     }
 }
