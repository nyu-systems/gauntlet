--- dumps/p4_16_samples/mux-bmv2.p4/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 17:31:24.631733200 +0200
+++ dumps/p4_16_samples/mux-bmv2.p4/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:31:24.634172400 +0200
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
