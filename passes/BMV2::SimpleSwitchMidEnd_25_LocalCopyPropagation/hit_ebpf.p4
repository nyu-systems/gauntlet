--- before_pass
+++ after_pass
@@ -67,8 +67,6 @@ control pipe(inout Headers_t headers, ou
         }
         if (!hasReturned_0) {
             tmp_0 = Check_src_ip.apply().hit;
-            if (tmp_0) 
-                pass = pass;
         }
     }
 }
