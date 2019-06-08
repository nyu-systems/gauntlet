--- before_pass
+++ after_pass
@@ -21,7 +21,7 @@ control Eg(inout Headers hdrs, inout Met
         val = res;
         tmp_0 = res[31:0];
         tmp_0 = tmp_0;
-        val[31:0] = tmp_0;
+        val = val & ~64w0xffffffff | (bit<64>)tmp_0 << 0 & 64w0xffffffff;
         res = val;
     }
     apply {
