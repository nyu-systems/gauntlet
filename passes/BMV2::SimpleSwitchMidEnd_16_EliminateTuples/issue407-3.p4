--- dumps/pruned/issue407-3-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-06-08 18:32:25.646892100 +0200
+++ dumps/pruned/issue407-3-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-06-08 18:32:25.650145600 +0200
@@ -16,7 +16,11 @@ header Ethernet_h {
     EthernetAddress srcAddr;
     bit<16>         etherType;
 }
-typedef tuple<bit<8>, bit<16>> myTuple0;
+struct tuple_0 {
+    bit<8>  field;
+    bit<16> field_0;
+}
+typedef tuple_0 myTuple0;
 struct myStruct1 {
     bit<7>          x1;
     int<33>         x2;
