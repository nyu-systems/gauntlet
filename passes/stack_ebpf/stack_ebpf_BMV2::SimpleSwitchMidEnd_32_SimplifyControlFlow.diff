--- before_pass
+++ after_pass
@@ -60,16 +60,12 @@ control pipe(inout Headers_t headers, ou
     }
     apply {
         pass = true;
-        {
-            {
-                key_0 = headers.ipv4[0].srcAddr;
-                switch (Check_src_ip_0.apply().action_run) {
-                    Reject: {
-                        pass = false;
-                    }
-                    NoAction_0: {
-                    }
-                }
+        key_0 = headers.ipv4[0].srcAddr;
+        switch (Check_src_ip_0.apply().action_run) {
+            Reject: {
+                pass = false;
+            }
+            NoAction_0: {
             }
         }
     }
