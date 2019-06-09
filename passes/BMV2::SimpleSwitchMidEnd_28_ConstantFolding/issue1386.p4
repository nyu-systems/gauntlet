--- before_pass
+++ after_pass
@@ -39,8 +39,7 @@ control ingress(inout Headers h, inout M
             if (!h.h.isValid()) 
                 c_hasReturned = true;
             if (!c_hasReturned) 
-                if (8w0 > 8w0) 
-                    h.h.setValid();
+                ;
         }
         sm.egress_spec = 9w0;
     }
