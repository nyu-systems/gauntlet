--- before_pass
+++ after_pass
@@ -26,9 +26,9 @@ extern bs {
 struct Packet_data {
 }
 control Q_pipe(inout TArg1 qArg1, inout TArg2 qArg2) {
+    bit<9> barg;
     @name(".NoAction") action NoAction_0() {
     }
-    bit<9> barg;
     @name("Q_pipe.p1.thost.B_action") action p1_thost_B_action_0(BParamType bData) {
         barg = bData;
         qArg1.field1 = barg;
