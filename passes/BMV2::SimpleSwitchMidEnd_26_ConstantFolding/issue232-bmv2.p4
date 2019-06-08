--- dumps/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:18.046896300 +0200
+++ dumps/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-06-08 18:32:18.050332200 +0200
@@ -32,9 +32,9 @@ control Eg(inout Headers hdrs, inout Met
             {
                 {
                     {
-                        val_2.field1 = (!false && 32w1 == 32w0 ? 32w0 : val_2.field1);
+                        val_2.field1 = val_2.field1;
                     }
-                    val_2.field1 = (!false && 32w1 == 32w0 ? 32w8 : val_2.field1);
+                    val_2.field1 = val_2.field1;
                     {
                     }
                 }
