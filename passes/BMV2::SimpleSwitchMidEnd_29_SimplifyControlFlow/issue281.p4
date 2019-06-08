--- before_pass
+++ after_pass
@@ -50,16 +50,12 @@ parser MyParser(packet_in b, out h hdr,
         l2_ether_0.setInvalid();
         b.extract<ethernet_t>(l2_ether_0);
         hdr_2_ether = l2_ether_0;
-        {
-            hdr.ether = hdr_2_ether;
-            hdr.vlan = hdr_2_vlan;
-            hdr.ipv4 = hdr_2_ipv4;
-        }
-        {
-            hdr_3_ether = hdr.ether;
-            hdr_3_vlan = hdr.vlan;
-            hdr_3_ipv4 = hdr.ipv4;
-        }
+        hdr.ether = hdr_2_ether;
+        hdr.vlan = hdr_2_vlan;
+        hdr.ipv4 = hdr_2_ipv4;
+        hdr_3_ether = hdr.ether;
+        hdr_3_vlan = hdr.vlan;
+        hdr_3_ipv4 = hdr.ipv4;
         transition L3_start;
     }
     state L3_start {
@@ -83,11 +79,9 @@ parser MyParser(packet_in b, out h hdr,
         transition L3_start;
     }
     state start_2 {
-        {
-            hdr.ether = hdr_3_ether;
-            hdr.vlan = hdr_3_vlan;
-            hdr.ipv4 = hdr_3_ipv4;
-        }
+        hdr.ether = hdr_3_ether;
+        hdr.vlan = hdr_3_vlan;
+        hdr.ipv4 = hdr_3_ipv4;
         transition accept;
     }
 }
