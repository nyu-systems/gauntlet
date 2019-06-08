--- before_pass
+++ after_pass
@@ -10,7 +10,7 @@ control c(inout bit<32> b) {
     apply {
         switch (t.apply().action_run) {
             a_0: {
-                b[6:3] = 4w1;
+                b = b & ~32w0x78 | (bit<32>)4w1 << 3 & 32w0x78;
             }
         }
     }
