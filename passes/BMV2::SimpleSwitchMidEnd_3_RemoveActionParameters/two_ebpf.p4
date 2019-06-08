--- before_pass
+++ after_pass
@@ -39,10 +39,11 @@ parser prs(packet_in p, out Headers_t he
     }
 }
 control pipe(inout Headers_t headers, out bool pass) {
-    @name(".NoAction") action NoAction_0() {
-    }
     IPv4Address address;
     bool pass_1;
+    bool hasReturned_0;
+    @name(".NoAction") action NoAction_0() {
+    }
     @name("pipe.c1.Reject") action c1_Reject() {
         pass_1 = false;
     }
@@ -58,7 +59,7 @@ control pipe(inout Headers_t headers, ou
         const default_action = NoAction_0();
     }
     apply {
-        bool hasReturned_0 = false;
+        hasReturned_0 = false;
         pass = true;
         if (!headers.ipv4.isValid()) {
             pass = false;
