--- before_pass
+++ after_pass
@@ -19,8 +19,9 @@ parser prs(packet_in p, out Headers h) {
     }
 }
 control c(inout Headers h) {
+    bool hasReturned_0;
     apply {
-        bool hasReturned_0 = false;
+        hasReturned_0 = false;
         if (!h.eth.isValid()) 
             hasReturned_0 = true;
         if (!hasReturned_0) 
