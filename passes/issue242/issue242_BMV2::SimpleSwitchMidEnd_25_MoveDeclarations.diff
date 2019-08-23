--- before_pass
+++ after_pass
@@ -53,6 +53,10 @@ control Eg(inout Headers hdrs, inout Met
     bit<32> inc_0;
     bit<32> tmp;
     bit<32> tmp_0;
+    bool cond;
+    bool pred;
+    bool cond_0;
+    bool pred_0;
     @name("Eg.debug") register<bit<32>>(32w100) debug_0;
     @name("Eg.reg") register<bit<32>>(32w1) reg_0;
     @name("Eg.test") action test() {
@@ -61,9 +65,7 @@ control Eg(inout Headers hdrs, inout Met
         }
         _pred_0 = val_0.field1 != 32w0;
         {
-            bool cond;
             {
-                bool pred;
                 cond = _pred_0;
                 pred = cond;
                 tmp = (pred ? 32w1 : tmp);
@@ -74,9 +76,7 @@ control Eg(inout Headers hdrs, inout Met
         }
         inc_0 = tmp;
         {
-            bool cond_0;
             {
-                bool pred_0;
                 cond_0 = _pred_0;
                 pred_0 = cond_0;
                 tmp_0 = (pred_0 ? 32w1 : tmp_0);
