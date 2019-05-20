--- dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:30:36.372212600 +0200
+++ dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:30:36.424228700 +0200
@@ -22,24 +22,8 @@ control Ing(inout Headers headers, inout
 control Eg(inout Headers hdrs, inout Metadata meta, inout standard_metadata_t standard_meta) {
     Value val_2;
     @name("Eg.test") action test_0() {
-        {
-        }
-        {
-        }
-        {
-        }
-        {
-            {
-                {
-                    {
-                        val_2.field1 = val_2.field1;
-                    }
-                    val_2.field1 = val_2.field1;
-                    {
-                    }
-                }
-            }
-        }
+        val_2.field1 = val_2.field1;
+        val_2.field1 = val_2.field1;
     }
     apply {
         test_0();
