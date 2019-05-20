--- dumps/p4_16_samples/newtype2.p4/pruned/newtype2-BMV2::SimpleSwitchMidEnd_0_CheckTableSize.p4	2019-05-20 17:31:27.605165700 +0200
+++ dumps/p4_16_samples/newtype2.p4/pruned/newtype2-BMV2::SimpleSwitchMidEnd_1_EliminateNewtype.p4	2019-05-20 17:31:27.637159400 +0200
@@ -1,6 +1,6 @@
 #include <core.p4>
 typedef bit<9> PortIdUInt_t;
-type bit<9> PortId_t;
+typedef bit<9> PortId_t;
 struct M {
     PortId_t     e;
     PortIdUInt_t es;
