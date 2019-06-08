--- before_pass
+++ after_pass
@@ -59,13 +59,11 @@ control pipe(inout Headers_t headers, ou
     }
     apply {
         pass = true;
-        {
-            switch (Check_src_ip.apply().action_run) {
-                Reject_0: {
-                    pass = false;
-                }
-                NoAction_0: {
-                }
+        switch (Check_src_ip.apply().action_run) {
+            Reject_0: {
+                pass = false;
+            }
+            NoAction_0: {
             }
         }
     }
