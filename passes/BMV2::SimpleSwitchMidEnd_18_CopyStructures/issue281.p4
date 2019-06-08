--- dumps/pruned/issue281-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:32:20.652579100 +0200
+++ dumps/pruned/issue281-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:32:20.656336400 +0200
@@ -46,8 +46,16 @@ parser MyParser(packet_in b, out h hdr,
         l2_ether_0.setInvalid();
         b.extract<ethernet_t>(l2_ether_0);
         hdr_2.ether = l2_ether_0;
-        hdr = hdr_2;
-        hdr_3 = hdr;
+        {
+            hdr.ether = hdr_2.ether;
+            hdr.vlan = hdr_2.vlan;
+            hdr.ipv4 = hdr_2.ipv4;
+        }
+        {
+            hdr_3.ether = hdr.ether;
+            hdr_3.vlan = hdr.vlan;
+            hdr_3.ipv4 = hdr.ipv4;
+        }
         transition L3_start;
     }
     state L3_start {
@@ -71,7 +79,11 @@ parser MyParser(packet_in b, out h hdr,
         transition L3_start;
     }
     state start_2 {
-        hdr = hdr_3;
+        {
+            hdr.ether = hdr_3.ether;
+            hdr.vlan = hdr_3.vlan;
+            hdr.ipv4 = hdr_3.ipv4;
+        }
         transition accept;
     }
 }
