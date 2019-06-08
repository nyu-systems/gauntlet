--- before_pass
+++ after_pass
@@ -66,7 +66,10 @@ control pipe(inout Headers_t headers, ou
             hasReturned_0 = true;
         }
         if (!hasReturned_0) 
-            tmp_0 = Check_src_ip.apply().hit;
+            if (Check_src_ip.apply().hit) 
+                tmp_0 = true;
+            else 
+                tmp_0 = false;
     }
 }
 ebpfFilter<Headers_t>(prs(), pipe()) main;
