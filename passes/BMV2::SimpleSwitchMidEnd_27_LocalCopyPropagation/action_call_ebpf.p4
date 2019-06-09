--- before_pass
+++ after_pass
@@ -9,10 +9,8 @@ parser prs(packet_in p, out Headers_t he
 }
 control pipe(inout Headers_t headers, out bool pass) {
     bool x_0;
-    bool rej;
     @name("pipe.Reject") action Reject() {
-        rej = x_0;
-        pass = rej;
+        pass = x_0;
     }
     apply {
         x_0 = true;
