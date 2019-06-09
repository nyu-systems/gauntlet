--- before_pass
+++ after_pass
@@ -28,8 +28,10 @@ struct Packet_data {
 control Q_pipe(inout TArg1 qArg1, inout TArg2 qArg2) {
     @name(".NoAction") action NoAction_0() {
     }
-    @name("Q_pipe.p1.thost.B_action") action p1_thost_B_action_0(out bit<9> barg, BParamType bData) {
+    bit<9> barg;
+    @name("Q_pipe.p1.thost.B_action") action p1_thost_B_action_0(BParamType bData) {
         barg = bData;
+        qArg1.field1 = barg;
     }
     @name("Q_pipe.p1.thost.C_action") action p1_thost_C_action_0(bit<9> cData) {
         qArg1.field1 = cData;
@@ -40,7 +42,7 @@ control Q_pipe(inout TArg1 qArg1, inout
             qArg2.field2: exact @name("aArg2.field2") ;
         }
         actions = {
-            p1_thost_B_action_0(qArg1.field1);
+            p1_thost_B_action_0();
             p1_thost_C_action_0();
         }
         size = 32w5;
