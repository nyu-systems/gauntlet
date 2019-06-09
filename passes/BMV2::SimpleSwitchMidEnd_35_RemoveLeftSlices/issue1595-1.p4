--- before_pass
+++ after_pass
@@ -11,7 +11,7 @@ control c(inout bit<32> b) {
     apply {
         switch (t_0.apply().action_run) {
             a: {
-                b[6:3] = 4w1;
+                b = b & ~32w0x78 | (bit<32>)4w1 << 3 & 32w0x78;
             }
         }
     }
