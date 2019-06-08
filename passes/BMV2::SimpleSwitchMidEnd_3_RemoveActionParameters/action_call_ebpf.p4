--- before_pass
+++ after_pass
@@ -9,12 +9,14 @@ parser prs(packet_in p, out Headers_t he
 }
 control pipe(inout Headers_t headers, out bool pass) {
     bool x;
-    @name("pipe.Reject") action Reject_0(bool rej) {
+    bool rej;
+    @name("pipe.Reject") action Reject_0() {
+        rej = x;
         pass = rej;
     }
     apply {
         x = true;
-        Reject_0(x);
+        Reject_0();
     }
 }
 ebpfFilter<Headers_t>(prs(), pipe()) main;
