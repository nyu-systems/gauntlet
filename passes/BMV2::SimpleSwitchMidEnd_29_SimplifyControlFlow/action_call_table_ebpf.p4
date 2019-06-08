--- before_pass
+++ after_pass
@@ -9,17 +9,9 @@ parser prs(packet_in p, out Headers_t he
 }
 control pipe(inout Headers_t headers, out bool pass) {
     @name("pipe.Reject") action Reject_0(bit<8> rej, bit<8> bar) {
-        {
-            {
-                pass = (rej == 8w0 ? true : pass);
-                pass = (!(rej == 8w0) ? false : pass);
-            }
-        }
-        {
-            {
-                pass = (bar == 8w0 ? false : pass);
-            }
-        }
+        pass = (rej == 8w0 ? true : pass);
+        pass = (!(rej == 8w0) ? false : pass);
+        pass = (bar == 8w0 ? false : pass);
     }
     @name("pipe.t") table t {
         actions = {
