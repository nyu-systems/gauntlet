--- before_pass
+++ after_pass
@@ -46,9 +46,10 @@ control pipe(inout Headers_t headers, ou
         pass = false;
         headers.ipv4[0].srcAddr = add;
     }
+    bit<32> key_0;
     @name("pipe.Check_src_ip") table Check_src_ip_0 {
         key = {
-            headers.ipv4[0].srcAddr: exact @name("headers.ipv4[0].srcAddr") ;
+            key_0: exact @name("headers.ipv4[0].srcAddr") ;
         }
         actions = {
             Reject();
@@ -60,11 +61,14 @@ control pipe(inout Headers_t headers, ou
     apply {
         pass = true;
         {
-            switch (Check_src_ip_0.apply().action_run) {
-                Reject: {
-                    pass = false;
-                }
-                NoAction_0: {
+            {
+                key_0 = headers.ipv4[0].srcAddr;
+                switch (Check_src_ip_0.apply().action_run) {
+                    Reject: {
+                        pass = false;
+                    }
+                    NoAction_0: {
+                    }
                 }
             }
         }
