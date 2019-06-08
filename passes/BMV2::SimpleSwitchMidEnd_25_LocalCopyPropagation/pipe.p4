--- dumps/pruned/pipe-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:34:08.304162100 +0200
+++ dumps/pruned/pipe-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:34:08.306361300 +0200
@@ -28,12 +28,10 @@ struct Packet_data {
 control Q_pipe(inout TArg1 qArg1, inout TArg2 qArg2) {
     TArg1 p1_tArg1_0;
     TArg2 p1_aArg2_0;
-    bit<9> barg;
     @name(".NoAction") action NoAction_0() {
     }
     @name("Q_pipe.p1.thost.B_action") action p1_thost_B_action(BParamType bData) {
-        barg = bData;
-        p1_tArg1_0.field1 = barg;
+        p1_tArg1_0.field1 = bData;
     }
     @name("Q_pipe.p1.thost.C_action") action p1_thost_C_action(bit<9> cData) {
         p1_tArg1_0.field1 = cData;
@@ -55,7 +53,7 @@ control Q_pipe(inout TArg1 qArg1, inout
     }
     @name("Q_pipe.p1.Tinner") table p1_Tinner_0 {
         key = {
-            qArg1.field1: ternary @name("pArg1.field1") ;
+            p1_tArg1_0.field1: ternary @name("pArg1.field1") ;
         }
         actions = {
             p1_Drop();
@@ -74,10 +72,8 @@ control Q_pipe(inout TArg1 qArg1, inout
         p1_thost_T_0.apply();
         {
             qArg1.field1 = p1_tArg1_0.field1;
-            qArg1.drop = p1_tArg1_0.drop;
         }
         {
-            p1_tArg1_0.field1 = qArg1.field1;
             p1_tArg1_0.drop = qArg1.drop;
         }
         {
@@ -86,7 +82,6 @@ control Q_pipe(inout TArg1 qArg1, inout
         p1_thost_T_0.apply();
         {
             qArg1.field1 = p1_tArg1_0.field1;
-            qArg1.drop = p1_tArg1_0.drop;
         }
         p1_Tinner_0.apply();
     }
