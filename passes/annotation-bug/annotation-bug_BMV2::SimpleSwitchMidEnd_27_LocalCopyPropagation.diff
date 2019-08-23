--- before_pass
+++ after_pass
@@ -15,12 +15,8 @@ struct tuple_0 {
 extern bit<16> get<T>(in T data);
 control cc() {
     ipv4_option_timestamp_t hdr_0_ipv4_option_timestamp;
-    ipv4_option_timestamp_t tmp_ipv4_option_timestamp;
     apply {
-        {
-            tmp_ipv4_option_timestamp = hdr_0_ipv4_option_timestamp;
-        }
-        get<headers>({ tmp_ipv4_option_timestamp });
+        get<headers>({ hdr_0_ipv4_option_timestamp });
     }
 }
 control C();
