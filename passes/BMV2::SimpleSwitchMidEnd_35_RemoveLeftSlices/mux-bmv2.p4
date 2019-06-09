--- before_pass
+++ after_pass
@@ -21,7 +21,7 @@ control Eg(inout Headers hdrs, inout Met
         val = res_0;
         tmp = res_0[31:0];
         tmp = tmp;
-        val[31:0] = tmp;
+        val = val & ~64w0xffffffff | (bit<64>)tmp << 0 & 64w0xffffffff;
         res_0 = val;
     }
     apply {
