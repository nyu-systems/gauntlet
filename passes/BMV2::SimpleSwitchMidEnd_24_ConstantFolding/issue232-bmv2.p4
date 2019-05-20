--- dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:30:36.354738600 +0200
+++ dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:30:36.357686800 +0200
@@ -36,7 +36,7 @@ control Eg(inout Headers hdrs, inout Met
         {
             defaultKey.field1 = 32w0;
         }
-        same = true && inKey.field1 == defaultKey.field1;
+        same = inKey.field1 == defaultKey.field1;
         {
             val_1.field1 = 32w0;
         }
