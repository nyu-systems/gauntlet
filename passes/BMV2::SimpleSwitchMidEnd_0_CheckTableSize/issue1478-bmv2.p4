--- before_pass
+++ after_pass
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
