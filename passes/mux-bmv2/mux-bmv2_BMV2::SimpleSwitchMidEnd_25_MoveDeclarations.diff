--- before_pass
+++ after_pass
@@ -19,14 +19,14 @@ control Eg(inout Headers hdrs, inout Met
     bit<32> tmp;
     bool p_1;
     bit<64> val;
+    bool cond;
+    bool pred;
     @name("Eg.update") action update() {
         p_1 = true;
         val = res_0;
         _sub_0 = val[31:0];
         {
-            bool cond;
             {
-                bool pred;
                 cond = p_1;
                 pred = cond;
                 tmp = (pred ? _sub_0 : tmp);
