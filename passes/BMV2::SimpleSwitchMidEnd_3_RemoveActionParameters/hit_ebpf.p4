--- before_pass
+++ after_pass
@@ -39,9 +39,10 @@ parser prs(packet_in p, out Headers_t he
     }
 }
 control pipe(inout Headers_t headers, out bool pass) {
+    bool tmp;
+    bool hasReturned;
     @name(".NoAction") action NoAction_0() {
     }
-    bool tmp;
     @name("pipe.Reject") action Reject(IPv4Address add) {
         pass = false;
         headers.ipv4.srcAddr = add;
@@ -58,7 +59,7 @@ control pipe(inout Headers_t headers, ou
         const default_action = NoAction_0();
     }
     apply {
-        bool hasReturned = false;
+        hasReturned = false;
         pass = true;
         if (!headers.ipv4.isValid()) {
             pass = false;
