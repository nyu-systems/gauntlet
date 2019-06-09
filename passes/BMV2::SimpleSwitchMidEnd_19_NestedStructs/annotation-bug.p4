--- before_pass
+++ after_pass
@@ -14,13 +14,13 @@ struct tuple_0 {
 }
 extern bit<16> get<T>(in T data);
 control cc() {
-    headers hdr_0;
-    headers tmp;
+    ipv4_option_timestamp_t hdr_0_ipv4_option_timestamp;
+    ipv4_option_timestamp_t tmp_ipv4_option_timestamp;
     apply {
         {
-            tmp.ipv4_option_timestamp = hdr_0.ipv4_option_timestamp;
+            tmp_ipv4_option_timestamp = hdr_0_ipv4_option_timestamp;
         }
-        get<headers>(tmp);
+        get<headers>({ tmp_ipv4_option_timestamp });
     }
 }
 control C();
