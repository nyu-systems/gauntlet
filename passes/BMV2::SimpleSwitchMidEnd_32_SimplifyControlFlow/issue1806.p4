--- before_pass
+++ after_pass
@@ -30,12 +30,8 @@ control c(inout Headers h, inout standar
         default_action = NoAction_0();
     }
     apply {
-        {
-            {
-                key_0 = h.eth.tst[13:4];
-                tns_0.apply();
-            }
-        }
+        key_0 = h.eth.tst[13:4];
+        tns_0.apply();
     }
 }
 parser p<H>(packet_in _p, out H h);
