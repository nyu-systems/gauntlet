--- dumps/p4_16_samples/issue1897-bmv2.p4/pruned/issue1897-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:30:35.316332800 +0200
+++ dumps/p4_16_samples/issue1897-bmv2.p4/pruned/issue1897-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:30:35.318620800 +0200
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
