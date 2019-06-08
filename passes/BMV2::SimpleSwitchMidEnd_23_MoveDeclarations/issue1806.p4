--- dumps/pruned/issue1806-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-06-08 18:32:14.085398600 +0200
+++ dumps/pruned/issue1806-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-06-08 18:32:14.089324500 +0200
@@ -14,11 +14,11 @@ parser prs(packet_in p, out Headers h) {
     }
 }
 control c(inout Headers h, inout standard_metadata_t sm) {
+    bit<10> key_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("c.do_act") action do_act_0() {
     }
-    bit<10> key_0;
     @name("c.tns") table tns {
         key = {
             key_0: exact @name("h.eth.tst[13:4]") ;
