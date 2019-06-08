--- dumps/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-06-08 18:32:58.155156000 +0200
+++ dumps/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-06-08 18:32:58.158912000 +0200
@@ -19,14 +19,14 @@ control Eg(inout Headers hdrs, inout Met
     bit<32> tmp_0;
     bool p_1;
     bit<64> val;
+    bool cond;
+    bool pred;
     @name("Eg.update") action update_0() {
         p_1 = true;
         val = res;
         _sub = val[31:0];
         {
-            bool cond;
             {
-                bool pred;
                 cond = p_1;
                 pred = cond;
                 tmp_0 = (pred ? _sub : tmp_0);
