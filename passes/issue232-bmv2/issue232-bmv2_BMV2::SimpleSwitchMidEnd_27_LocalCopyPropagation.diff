--- before_pass
+++ after_pass
@@ -20,40 +20,15 @@ control Ing(inout Headers headers, inout
     }
 }
 control Eg(inout Headers hdrs, inout Metadata meta, inout standard_metadata_t standard_meta) {
-    Key inKey_0;
-    Key defaultKey_0;
-    bool same_0;
-    Value val;
-    bool done_0;
-    bool ok_0;
     Value val_0;
-    bool cond;
-    bool pred;
     @name("Eg.test") action test() {
         {
-            inKey_0.field1 = 32w1;
-        }
-        {
-            defaultKey_0.field1 = 32w0;
-        }
-        same_0 = inKey_0.field1 == defaultKey_0.field1;
-        {
-            val.field1 = 32w0;
-        }
-        done_0 = false;
-        ok_0 = !done_0 && same_0;
-        {
             {
-                cond = ok_0;
-                pred = cond;
                 {
                     {
-                        val_0.field1 = (pred ? val.field1 : val_0.field1);
-                    }
-                    val_0.field1 = (pred ? 32w8 : val_0.field1);
-                    {
-                        val.field1 = (pred ? val_0.field1 : val.field1);
+                        val_0.field1 = (!false && 32w1 == 32w0 ? 32w0 : val_0.field1);
                     }
+                    val_0.field1 = (!false && 32w1 == 32w0 ? 32w8 : val_0.field1);
                 }
             }
         }
