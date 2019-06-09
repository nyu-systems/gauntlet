--- before_pass
+++ after_pass
@@ -66,7 +66,10 @@ control pipe(inout Headers_t headers, ou
             hasReturned = true;
         }
         if (!hasReturned) 
-            tmp = Check_src_ip_0.apply().hit;
+            if (Check_src_ip_0.apply().hit) 
+                tmp = true;
+            else 
+                tmp = false;
     }
 }
 ebpfFilter<Headers_t>(prs(), pipe()) main;
