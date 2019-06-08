--- before_pass
+++ after_pass
@@ -29,9 +29,7 @@ control c(inout Headers h, inout standar
         default_action = NoAction_0();
     }
     apply {
-        {
-            tns.apply();
-        }
+        tns.apply();
     }
 }
 parser p<H>(packet_in _p, out H h);
