--- dumps/pruned/serenum-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:33:33.154601300 +0200
+++ dumps/pruned/serenum-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:33:33.178374200 +0200
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
