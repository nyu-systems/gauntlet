--- before_pass
+++ after_pass
@@ -1,31 +1,31 @@
 #include <core.p4>
 #include <v1model.p4>
 typedef bit<48> Eth0_t;
-type bit<48> Eth1_t;
-@p4runtime_translation("mycompany.com/EthernetAddress" , 49) type bit<48> Eth2_t;
+typedef bit<48> Eth1_t;
+typedef bit<48> Eth2_t;
 typedef bit<8> Custom0_t;
-type bit<8> Custom1_t;
-@p4runtime_translation("mycompany.com/My_Byte2" , 12) type bit<8> Custom2_t;
+typedef bit<8> Custom1_t;
+typedef bit<8> Custom2_t;
 typedef Custom0_t Custom00_t;
-type Custom0_t Custom01_t;
-@p4runtime_translation("mycompany.com/My_Byte3" , 13) type Custom0_t Custom02_t;
+typedef Custom0_t Custom01_t;
+typedef Custom0_t Custom02_t;
 typedef Custom1_t Custom10_t;
-type Custom1_t Custom11_t;
-@p4runtime_translation("mycompany.com/My_Byte4" , 14) type Custom1_t Custom12_t;
+typedef Custom1_t Custom11_t;
+typedef Custom1_t Custom12_t;
 typedef Custom2_t Custom20_t;
-type Custom2_t Custom21_t;
-@p4runtime_translation("mycompany.com/My_Byte5" , 15) type Custom2_t Custom22_t;
-type Custom00_t Custom001_t;
-@p4runtime_translation("mycompany.com/My_Byte6" , 16) type Custom00_t Custom002_t;
-type Custom10_t Custom101_t;
-@p4runtime_translation("mycompany.com/My_Byte7" , 17) type Custom10_t Custom102_t;
-type Custom20_t Custom201_t;
-@p4runtime_translation("mycompany.com/My_Byte8" , 18) type Custom20_t Custom202_t;
+typedef Custom2_t Custom21_t;
+typedef Custom2_t Custom22_t;
+typedef Custom00_t Custom001_t;
+typedef Custom00_t Custom002_t;
+typedef Custom10_t Custom101_t;
+typedef Custom10_t Custom102_t;
+typedef Custom20_t Custom201_t;
+typedef Custom20_t Custom202_t;
 typedef Custom22_t Custom220_t;
 typedef Custom002_t Custom0020_t;
 typedef Custom0020_t Custom00200_t;
-type Custom00200_t Custom002001_t;
-@p4runtime_translation("mycompany.com/My_Byte9" , 19) type Custom00200_t Custom002002_t;
+typedef Custom00200_t Custom002001_t;
+typedef Custom00200_t Custom002002_t;
 typedef Custom002001_t Custom0020010_t;
 typedef Custom002002_t Custom0020020_t;
 enum bit<8> serenum_t {
