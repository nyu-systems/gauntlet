--- before_pass
+++ after_pass
@@ -9,12 +9,14 @@ parser prs(packet_in p, out Headers_t he
 }
 control pipe(inout Headers_t headers, out bool pass) {
     bool x_0;
-    @name("pipe.Reject") action Reject(bool rej) {
+    bool rej;
+    @name("pipe.Reject") action Reject() {
+        rej = x_0;
         pass = rej;
     }
     apply {
         x_0 = true;
-        Reject(x_0);
+        Reject();
     }
 }
 ebpfFilter<Headers_t>(prs(), pipe()) main;
