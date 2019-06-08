--- dumps/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-06-08 18:32:18.038766200 +0200
+++ dumps/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:32:18.042938900 +0200
@@ -36,7 +36,7 @@ control Eg(inout Headers hdrs, inout Met
         {
             defaultKey.field1 = 32w0;
         }
-        same = true && inKey.field1 == defaultKey.field1;
+        same = inKey.field1 == defaultKey.field1;
         {
             val_1.field1 = 32w0;
         }
