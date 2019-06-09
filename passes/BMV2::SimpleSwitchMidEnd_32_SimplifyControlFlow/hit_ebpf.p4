--- before_pass
+++ after_pass
@@ -65,9 +65,8 @@ control pipe(inout Headers_t headers, ou
             pass = false;
             hasReturned = true;
         }
-        if (!hasReturned) {
+        if (!hasReturned) 
             tmp = Check_src_ip_0.apply().hit;
-        }
     }
 }
 ebpfFilter<Headers_t>(prs(), pipe()) main;
