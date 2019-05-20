--- dumps/p4_16_samples/issue1814-bmv2.p4/pruned/issue1814-bmv2-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:30:31.267098800 +0200
+++ dumps/p4_16_samples/issue1814-bmv2.p4/pruned/issue1814-bmv2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:30:31.290320400 +0200
@@ -11,9 +11,9 @@ parser ParserImpl(packet_in packet, out
     }
 }
 control IngressImpl(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
+    bit<1> registerData;
     @name(".NoAction") action NoAction_0() {
     }
-    bit<1> registerData;
     @name("IngressImpl.testRegister") register<bit<1>>(32w1) testRegister;
     @name("IngressImpl.debug_table") table debug_table {
         key = {
