--- dumps/pruned/issue983-bmv2-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:32:50.979688400 +0200
+++ dumps/pruned/issue983-bmv2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:32:50.994344300 +0200
@@ -31,11 +31,11 @@ parser IngressParserImpl(packet_in buffe
     }
 }
 control ingress(inout headers hdr, inout metadata user_meta, inout standard_metadata_t standard_metadata) {
-    @name(".NoAction") action NoAction_0() {
-    }
     bit<16> tmp_1;
     bit<32> x1_1;
     bit<16> x2_1;
+    @name(".NoAction") action NoAction_0() {
+    }
     @name("ingress.debug_table_cksum1") table debug_table_cksum1 {
         key = {
             hdr.ethernet.srcAddr            : exact @name("hdr.ethernet.srcAddr") ;
