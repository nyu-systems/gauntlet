--- before_pass
+++ after_pass
@@ -38,20 +38,8 @@ parser MyParser(packet_in b, out h hdr,
         hdr.ether.setInvalid();
         hdr.vlan.setInvalid();
         hdr.ipv4.setInvalid();
-        transition L2_start;
-    }
-    state L2_start {
         hdr.ether.setInvalid();
-        transition L2_EthernetParser_start;
-    }
-    state L2_EthernetParser_start {
         b.extract<ethernet_t>(hdr.ether);
-        transition L2_start_0;
-    }
-    state L2_start_0 {
-        transition start_1;
-    }
-    state start_1 {
         transition L3_start;
     }
     state L3_start {
@@ -64,24 +52,12 @@ parser MyParser(packet_in b, out h hdr,
     }
     state L3_ipv4 {
         hdr.ipv4.setInvalid();
-        transition L3_Ipv4Parser_start;
-    }
-    state L3_Ipv4Parser_start {
         b.extract<ipv4_t>(hdr.ipv4);
-        transition L3_ipv4_0;
-    }
-    state L3_ipv4_0 {
         transition start_2;
     }
     state L3_vlan {
         hdr.vlan.setInvalid();
-        transition L3_VlanParser_start;
-    }
-    state L3_VlanParser_start {
         b.extract<vlan_t>(hdr.vlan);
-        transition L3_vlan_0;
-    }
-    state L3_vlan_0 {
         transition L3_start;
     }
     state start_2 {
