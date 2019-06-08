--- before_pass
+++ after_pass
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
