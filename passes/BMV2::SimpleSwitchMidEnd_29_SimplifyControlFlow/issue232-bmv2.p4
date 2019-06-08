--- before_pass
+++ after_pass
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
