--- before_pass
+++ after_pass
@@ -65,9 +65,8 @@ control pipe(inout Headers_t headers, ou
             pass = false;
             hasReturned_0 = true;
         }
-        if (!hasReturned_0) {
+        if (!hasReturned_0) 
             tmp_0 = Check_src_ip.apply().hit;
-        }
     }
 }
 ebpfFilter<Headers_t>(prs(), pipe()) main;
