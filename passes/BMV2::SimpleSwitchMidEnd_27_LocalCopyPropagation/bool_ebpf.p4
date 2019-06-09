--- before_pass
+++ after_pass
@@ -8,10 +8,8 @@ parser prs(packet_in p, out Headers_t he
     }
 }
 control pipe(inout Headers_t headers, out bool pass) {
-    bool x_0;
     apply {
-        x_0 = true;
-        pass = x_0 != false;
+        pass = true != false;
     }
 }
 ebpfFilter<Headers_t>(prs(), pipe()) main;
