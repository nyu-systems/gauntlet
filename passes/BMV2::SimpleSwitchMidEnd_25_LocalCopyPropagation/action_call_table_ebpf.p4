--- before_pass
+++ after_pass
@@ -8,26 +8,16 @@ parser prs(packet_in p, out Headers_t he
     }
 }
 control pipe(inout Headers_t headers, out bool pass) {
-    bool cond;
-    bool pred;
-    bool cond_0;
-    bool pred_0;
     @name("pipe.Reject") action Reject_0(bit<8> rej, bit<8> bar) {
         {
             {
-                cond = rej == 8w0;
-                pred = cond;
-                pass = (pred ? true : pass);
-                cond = !cond;
-                pred = cond;
-                pass = (pred ? false : pass);
+                pass = (rej == 8w0 ? true : pass);
+                pass = (!(rej == 8w0) ? false : pass);
             }
         }
         {
             {
-                cond_0 = bar == 8w0;
-                pred_0 = cond_0;
-                pass = (pred_0 ? false : pass);
+                pass = (bar == 8w0 ? false : pass);
             }
         }
     }
