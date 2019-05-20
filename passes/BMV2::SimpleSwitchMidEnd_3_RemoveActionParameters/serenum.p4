--- dumps/p4_16_samples/serenum.p4/pruned/serenum-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:31:58.622091800 +0200
+++ dumps/p4_16_samples/serenum.p4/pruned/serenum-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:31:58.642423000 +0200
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
