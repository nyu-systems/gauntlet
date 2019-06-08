--- before_pass
+++ after_pass
@@ -71,7 +71,6 @@ control pipe(inout Headers_t headers, ou
             c1_Check_ip_0.apply();
             pass = pass_1;
             address = headers.ipv4.dstAddr;
-            pass_1 = pass;
             c1_Check_ip_0.apply();
             pass = pass_1;
         }
