--- dumps/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:18.057748100 +0200
+++ dumps/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:18.128119400 +0200
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
