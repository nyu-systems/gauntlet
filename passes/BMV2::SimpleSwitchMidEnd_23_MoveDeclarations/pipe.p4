--- before_pass
+++ after_pass
@@ -28,9 +28,9 @@ struct Packet_data {
 control Q_pipe(inout TArg1 qArg1, inout TArg2 qArg2) {
     TArg1 p1_tArg1_0;
     TArg2 p1_aArg2_0;
+    bit<9> barg;
     @name(".NoAction") action NoAction_0() {
     }
-    bit<9> barg;
     @name("Q_pipe.p1.thost.B_action") action p1_thost_B_action(BParamType bData) {
         barg = bData;
         p1_tArg1_0.field1 = barg;
