--- before_pass
+++ after_pass
@@ -67,8 +67,6 @@ control pipe(inout Headers_t headers, ou
         }
         if (!hasReturned) {
             tmp = Check_src_ip_0.apply().hit;
-            if (tmp) 
-                pass = pass;
         }
     }
 }
