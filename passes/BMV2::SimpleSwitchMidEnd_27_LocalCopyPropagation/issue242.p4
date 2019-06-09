--- before_pass
+++ after_pass
@@ -48,48 +48,27 @@ control Ing(inout Headers headers, inout
     }
 }
 control Eg(inout Headers hdrs, inout Metadata meta, inout standard_metadata_t standard_meta) {
-    Value val_0;
-    bool _pred_0;
-    bit<32> inc_0;
     bit<32> tmp;
     bit<32> tmp_0;
-    bool cond;
-    bool pred;
-    bool cond_0;
-    bool pred_0;
     @name("Eg.debug") register<bit<32>>(32w100) debug_0;
     @name("Eg.reg") register<bit<32>>(32w1) reg_0;
     @name("Eg.test") action test() {
         {
-            val_0.field1 = 32w0;
-        }
-        _pred_0 = val_0.field1 != 32w0;
-        {
             {
-                cond = _pred_0;
-                pred = cond;
-                tmp = (pred ? 32w1 : tmp);
-                cond = !cond;
-                pred = cond;
-                tmp = (pred ? 32w0 : tmp);
+                tmp = (32w0 != 32w0 ? 32w1 : tmp);
+                tmp = (!(32w0 != 32w0) ? 32w0 : tmp);
             }
         }
-        inc_0 = tmp;
         {
             {
-                cond_0 = _pred_0;
-                pred_0 = cond_0;
-                tmp_0 = (pred_0 ? 32w1 : tmp_0);
-                cond_0 = !cond_0;
-                pred_0 = cond_0;
-                tmp_0 = (pred_0 ? 32w0 : tmp_0);
+                tmp_0 = (32w0 != 32w0 ? 32w1 : tmp_0);
+                tmp_0 = (!(32w0 != 32w0) ? 32w0 : tmp_0);
             }
         }
         debug_0.write(32w0, tmp_0);
-        debug_0.write(32w1, inc_0);
-        val_0.field1 = 32w1;
-        debug_0.write(32w2, inc_0);
-        reg_0.write(32w0, val_0.field1);
+        debug_0.write(32w1, tmp);
+        debug_0.write(32w2, tmp);
+        reg_0.write(32w0, 32w1);
     }
     apply {
         test();
