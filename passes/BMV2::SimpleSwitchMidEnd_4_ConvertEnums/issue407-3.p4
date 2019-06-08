--- dumps/pruned/issue407-3-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:32:25.725195600 +0200
+++ dumps/pruned/issue407-3-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-06-08 18:32:25.727479500 +0200
@@ -11,11 +11,6 @@ struct mystruct2 {
     bit<4>    a;
     bit<4>    b;
 }
-enum myenum1 {
-    MY_ENUM1_VAL1,
-    MY_ENUM1_VAL2,
-    MY_ENUM1_VAL3
-}
 header Ethernet_h {
     EthernetAddress dstAddr;
     EthernetAddress srcAddr;
@@ -31,7 +26,7 @@ struct myStruct1 {
     varbit<104>     x6;
     error           x7;
     bool            x8;
-    myenum1         x9;
+    bit<32>         x9;
     Ethernet_h      x10;
     Ethernet_h[4]   x11;
     mystruct1       x12;
