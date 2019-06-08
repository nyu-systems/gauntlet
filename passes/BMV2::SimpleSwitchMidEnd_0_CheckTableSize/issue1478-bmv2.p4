--- dumps/pruned/issue1478-bmv2-FrontEnd_49_FrontEndLast.p4	2019-06-08 18:32:03.312130000 +0200
+++ dumps/pruned/issue1478-bmv2-BMV2::SimpleSwitchMidEnd_0_CheckTableSize.p4	2019-06-08 18:32:03.089093700 +0200
@@ -33,7 +33,6 @@ control ingress(inout Headers h, inout M
     @name(".NoAction") action NoAction_3() {
     }
     @name("ingress.t1") table t1 {
-        size = 3;
         actions = {
             NoAction_0();
         }
@@ -49,7 +48,6 @@ control ingress(inout Headers h, inout M
         const entries = {
                         9w0 : NoAction_3();
         }
-        size = 10;
         default_action = NoAction_3();
     }
     apply {
