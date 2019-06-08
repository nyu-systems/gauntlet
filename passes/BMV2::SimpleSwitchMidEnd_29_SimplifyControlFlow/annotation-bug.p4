--- before_pass
+++ after_pass
@@ -16,8 +16,6 @@ extern bit<16> get<T>(in T data);
 control cc() {
     ipv4_option_timestamp_t hdr_1_ipv4_option_timestamp;
     apply {
-        {
-        }
         get<headers>({ hdr_1_ipv4_option_timestamp });
     }
 }
