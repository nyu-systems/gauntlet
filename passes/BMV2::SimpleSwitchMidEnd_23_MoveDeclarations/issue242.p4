--- dumps/pruned/issue242-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-06-08 18:32:18.696049200 +0200
+++ dumps/pruned/issue242-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-06-08 18:32:18.697953800 +0200
@@ -53,6 +53,10 @@ control Eg(inout Headers hdrs, inout Met
     bit<32> inc;
     bit<32> tmp_1;
     bit<32> tmp_2;
+    bool cond;
+    bool pred;
+    bool cond_0;
+    bool pred_0;
     @name("Eg.debug") register<bit<32>>(32w100) debug;
     @name("Eg.reg") register<bit<32>>(32w1) reg;
     @name("Eg.test") action test_0() {
@@ -61,9 +65,7 @@ control Eg(inout Headers hdrs, inout Met
         }
         _pred = val.field1 != 32w0;
         {
-            bool cond;
             {
-                bool pred;
                 cond = _pred;
                 pred = cond;
                 tmp_1 = (pred ? 32w1 : tmp_1);
@@ -74,9 +76,7 @@ control Eg(inout Headers hdrs, inout Met
         }
         inc = tmp_1;
         {
-            bool cond_0;
             {
-                bool pred_0;
                 cond_0 = _pred;
                 pred_0 = cond_0;
                 tmp_2 = (pred_0 ? 32w1 : tmp_2);
