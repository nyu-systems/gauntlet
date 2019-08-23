--- before_pass
+++ after_pass
@@ -22,16 +22,8 @@ control Ing(inout Headers headers, inout
 control Eg(inout Headers hdrs, inout Metadata meta, inout standard_metadata_t standard_meta) {
     Value val_0;
     @name("Eg.test") action test() {
-        {
-            {
-                {
-                    {
-                        val_0.field1 = val_0.field1;
-                    }
-                    val_0.field1 = val_0.field1;
-                }
-            }
-        }
+        val_0.field1 = val_0.field1;
+        val_0.field1 = val_0.field1;
     }
     apply {
         test();
