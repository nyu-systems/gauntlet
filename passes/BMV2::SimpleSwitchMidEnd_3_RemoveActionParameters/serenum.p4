--- before_pass
+++ after_pass
@@ -19,8 +19,9 @@ parser prs(packet_in p, out Headers h) {
     }
 }
 control c(inout Headers h) {
+    bool hasReturned;
     apply {
-        bool hasReturned = false;
+        hasReturned = false;
         if (!h.eth.isValid()) 
             hasReturned = true;
         if (!hasReturned) 
