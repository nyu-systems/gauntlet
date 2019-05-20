--- dumps/p4_16_samples/issue281.p4/pruned/issue281-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:30:39.639991700 +0200
+++ dumps/p4_16_samples/issue281.p4/pruned/issue281-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-05-20 17:30:39.776960600 +0200
@@ -33,33 +33,37 @@ struct h {
 struct m {
 }
 parser MyParser(packet_in b, out h hdr, inout m meta, inout standard_metadata_t std) {
-    h hdr_2;
+    ethernet_t hdr_2_ether;
+    vlan_t hdr_2_vlan;
+    ipv4_t hdr_2_ipv4;
     ethernet_t l2_ether_0;
-    h hdr_3;
+    ethernet_t hdr_3_ether;
+    vlan_t hdr_3_vlan;
+    ipv4_t hdr_3_ipv4;
     bit<16> l3_etherType_0;
     ipv4_t l3_ipv4_0;
     vlan_t l3_vlan_0;
     state start {
-        hdr_2.ether.setInvalid();
-        hdr_2.vlan.setInvalid();
-        hdr_2.ipv4.setInvalid();
+        hdr_2_ether.setInvalid();
+        hdr_2_vlan.setInvalid();
+        hdr_2_ipv4.setInvalid();
         l2_ether_0.setInvalid();
         b.extract<ethernet_t>(l2_ether_0);
-        hdr_2.ether = l2_ether_0;
+        hdr_2_ether = l2_ether_0;
         {
-            hdr.ether = hdr_2.ether;
-            hdr.vlan = hdr_2.vlan;
-            hdr.ipv4 = hdr_2.ipv4;
+            hdr.ether = hdr_2_ether;
+            hdr.vlan = hdr_2_vlan;
+            hdr.ipv4 = hdr_2_ipv4;
         }
         {
-            hdr_3.ether = hdr.ether;
-            hdr_3.vlan = hdr.vlan;
-            hdr_3.ipv4 = hdr.ipv4;
+            hdr_3_ether = hdr.ether;
+            hdr_3_vlan = hdr.vlan;
+            hdr_3_ipv4 = hdr.ipv4;
         }
         transition L3_start;
     }
     state L3_start {
-        l3_etherType_0 = hdr_3.ether.etherType;
+        l3_etherType_0 = hdr_3_ether.etherType;
         transition select(l3_etherType_0) {
             16w0x800: L3_ipv4;
             16w0x8100: L3_vlan;
@@ -69,20 +73,20 @@ parser MyParser(packet_in b, out h hdr,
     state L3_ipv4 {
         l3_ipv4_0.setInvalid();
         b.extract<ipv4_t>(l3_ipv4_0);
-        hdr_3.ipv4 = l3_ipv4_0;
+        hdr_3_ipv4 = l3_ipv4_0;
         transition start_2;
     }
     state L3_vlan {
         l3_vlan_0.setInvalid();
         b.extract<vlan_t>(l3_vlan_0);
-        hdr_3.vlan = l3_vlan_0;
+        hdr_3_vlan = l3_vlan_0;
         transition L3_start;
     }
     state start_2 {
         {
-            hdr.ether = hdr_3.ether;
-            hdr.vlan = hdr_3.vlan;
-            hdr.ipv4 = hdr_3.ipv4;
+            hdr.ether = hdr_3_ether;
+            hdr.vlan = hdr_3_vlan;
+            hdr.ipv4 = hdr_3_ipv4;
         }
         transition accept;
     }
