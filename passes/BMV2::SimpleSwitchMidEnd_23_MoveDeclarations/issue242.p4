--- dumps/p4_16_samples/issue242.p4/pruned/issue242-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 17:30:36.967605500 +0200
+++ dumps/p4_16_samples/issue242.p4/pruned/issue242-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:30:36.972876000 +0200
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
