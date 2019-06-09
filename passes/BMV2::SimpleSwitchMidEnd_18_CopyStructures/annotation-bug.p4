--- before_pass
+++ after_pass
@@ -17,7 +17,9 @@ control cc() {
     headers hdr_0;
     headers tmp;
     apply {
-        tmp = {hdr_0.ipv4_option_timestamp};
+        {
+            tmp.ipv4_option_timestamp = hdr_0.ipv4_option_timestamp;
+        }
         get<headers>(tmp);
     }
 }
