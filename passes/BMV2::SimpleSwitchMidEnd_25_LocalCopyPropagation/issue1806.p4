--- dumps/pruned/issue1806-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:32:14.093027200 +0200
+++ dumps/pruned/issue1806-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:14.095882400 +0200
@@ -14,14 +14,13 @@ parser prs(packet_in p, out Headers h) {
     }
 }
 control c(inout Headers h, inout standard_metadata_t sm) {
-    bit<10> key_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("c.do_act") action do_act_0() {
     }
     @name("c.tns") table tns {
         key = {
-            key_0: exact @name("h.eth.tst[13:4]") ;
+            h.eth.tst[13:4]: exact @name("h.eth.tst[13:4]") ;
         }
         actions = {
             do_act_0();
@@ -31,7 +30,6 @@ control c(inout Headers h, inout standar
     }
     apply {
         {
-            key_0 = h.eth.tst[13:4];
             tns.apply();
         }
     }
