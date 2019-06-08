--- before_pass
+++ after_pass
@@ -39,6 +39,7 @@ parser prs(packet_in p, out Headers_t he
     }
 }
 control pipe(inout Headers_t headers, out bool pass) {
+    bool hasReturned_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("pipe.Reject") action Reject_0(IPv4Address add) {
@@ -57,7 +58,7 @@ control pipe(inout Headers_t headers, ou
         const default_action = NoAction_0();
     }
     apply {
-        bool hasReturned_0 = false;
+        hasReturned_0 = false;
         pass = true;
         if (!headers.ipv4.isValid()) {
             pass = false;
