--- before_pass
+++ after_pass
@@ -17,7 +17,9 @@ control cc() {
     headers hdr_1;
     headers tmp_0;
     apply {
-        tmp_0 = { hdr_1.ipv4_option_timestamp };
+        {
+            tmp_0.ipv4_option_timestamp = hdr_1.ipv4_option_timestamp;
+        }
         get<headers>(tmp_0);
     }
 }
