--- dumps/pruned/newtype2-BMV2::SimpleSwitchMidEnd_0_CheckTableSize.p4	2019-06-08 18:33:01.321885500 +0200
+++ dumps/pruned/newtype2-BMV2::SimpleSwitchMidEnd_1_EliminateNewtype.p4	2019-06-08 18:33:01.365143900 +0200
@@ -1,6 +1,6 @@
 #include <core.p4>
 typedef bit<9> PortIdUInt_t;
-type bit<9> PortId_t;
+typedef bit<9> PortId_t;
 struct M {
     PortId_t     e;
     PortIdUInt_t es;
