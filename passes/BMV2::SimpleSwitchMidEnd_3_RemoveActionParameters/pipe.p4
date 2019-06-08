--- dumps/pruned/pipe-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:34:08.321506700 +0200
+++ dumps/pruned/pipe-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:34:08.345631500 +0200
@@ -26,12 +26,14 @@ extern bs {
 struct Packet_data {
 }
 control Q_pipe(inout TArg1 qArg1, inout TArg2 qArg2) {
-    @name(".NoAction") action NoAction_0() {
-    }
     TArg1 p1_tArg1_0;
     TArg2 p1_aArg2_0;
-    @name("Q_pipe.p1.thost.B_action") action p1_thost_B_action(out bit<9> barg, BParamType bData) {
+    @name(".NoAction") action NoAction_0() {
+    }
+    bit<9> barg;
+    @name("Q_pipe.p1.thost.B_action") action p1_thost_B_action(BParamType bData) {
         barg = bData;
+        p1_tArg1_0.field1 = barg;
     }
     @name("Q_pipe.p1.thost.C_action") action p1_thost_C_action(bit<9> cData) {
         p1_tArg1_0.field1 = cData;
@@ -42,7 +44,7 @@ control Q_pipe(inout TArg1 qArg1, inout
             p1_aArg2_0.field2: exact @name("aArg2.field2") ;
         }
         actions = {
-            p1_thost_B_action(p1_tArg1_0.field1);
+            p1_thost_B_action();
             p1_thost_C_action();
         }
         size = 32w5;
