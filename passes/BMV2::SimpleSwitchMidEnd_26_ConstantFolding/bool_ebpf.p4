--- before_pass
+++ after_pass
@@ -9,7 +9,7 @@ parser prs(packet_in p, out Headers_t he
 }
 control pipe(inout Headers_t headers, out bool pass) {
     apply {
-        pass = true != false;
+        pass = true;
     }
 }
 ebpfFilter<Headers_t>(prs(), pipe()) main;
