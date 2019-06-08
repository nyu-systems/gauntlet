--- before_pass
+++ after_pass
@@ -43,21 +43,9 @@ parser MyParser(packet_in b, out h hdr,
         hdr_2.ether.setInvalid();
         hdr_2.vlan.setInvalid();
         hdr_2.ipv4.setInvalid();
-        transition L2_start;
-    }
-    state L2_start {
         l2_ether_0.setInvalid();
-        transition L2_EthernetParser_start;
-    }
-    state L2_EthernetParser_start {
         b.extract<ethernet_t>(l2_ether_0);
-        transition L2_start_0;
-    }
-    state L2_start_0 {
         hdr_2.ether = l2_ether_0;
-        transition start_1;
-    }
-    state start_1 {
         hdr = hdr_2;
         hdr_3 = hdr;
         transition L3_start;
@@ -72,25 +60,13 @@ parser MyParser(packet_in b, out h hdr,
     }
     state L3_ipv4 {
         l3_ipv4_0.setInvalid();
-        transition L3_Ipv4Parser_start;
-    }
-    state L3_Ipv4Parser_start {
         b.extract<ipv4_t>(l3_ipv4_0);
-        transition L3_ipv4_0;
-    }
-    state L3_ipv4_0 {
         hdr_3.ipv4 = l3_ipv4_0;
         transition start_2;
     }
     state L3_vlan {
         l3_vlan_0.setInvalid();
-        transition L3_VlanParser_start;
-    }
-    state L3_VlanParser_start {
         b.extract<vlan_t>(l3_vlan_0);
-        transition L3_vlan_0;
-    }
-    state L3_vlan_0 {
         hdr_3.vlan = l3_vlan_0;
         transition L3_start;
     }
