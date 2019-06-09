--- before_pass
+++ after_pass
@@ -8,11 +8,13 @@ parser prs(packet_in p, out Headers_t he
     }
 }
 control pipe(inout Headers_t headers, out bool pass) {
+    bool cond;
+    bool pred;
+    bool cond_0;
+    bool pred_0;
     @name("pipe.Reject") action Reject(bit<8> rej, bit<8> bar) {
         {
-            bool cond;
             {
-                bool pred;
                 cond = rej == 8w0;
                 pred = cond;
                 pass = (pred ? true : pass);
@@ -22,9 +24,7 @@ control pipe(inout Headers_t headers, ou
             }
         }
         {
-            bool cond_0;
             {
-                bool pred_0;
                 cond_0 = bar == 8w0;
                 pred_0 = cond_0;
                 pass = (pred_0 ? false : pass);
