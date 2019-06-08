--- dumps/pruned/issue1814-bmv2-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:32:14.532611200 +0200
+++ dumps/pruned/issue1814-bmv2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:32:14.550065300 +0200
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
