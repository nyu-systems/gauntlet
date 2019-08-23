--- before_pass
+++ after_pass
@@ -64,11 +64,9 @@ control pipe(inout Headers_t headers, ou
         default_action = drop();
     }
     apply {
-        {
-            key_0 = headers.ipv4.srcAddr + 32w1;
-            key_1 = headers.ipv4.dstAddr + 32w1;
-            t_0.apply();
-        }
+        key_0 = headers.ipv4.srcAddr + 32w1;
+        key_1 = headers.ipv4.dstAddr + 32w1;
+        t_0.apply();
     }
 }
 ebpfFilter<Headers_t>(prs(), pipe()) main;
