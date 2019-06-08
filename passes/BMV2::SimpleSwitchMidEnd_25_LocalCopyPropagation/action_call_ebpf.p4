--- before_pass
+++ after_pass
@@ -9,10 +9,8 @@ parser prs(packet_in p, out Headers_t he
 }
 control pipe(inout Headers_t headers, out bool pass) {
     bool x;
-    bool rej;
     @name("pipe.Reject") action Reject_0() {
-        rej = x;
-        pass = rej;
+        pass = x;
     }
     apply {
         x = true;
