--- dumps/pruned/after-return-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:31:01.940776600 +0200
+++ dumps/pruned/after-return-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:31:01.981324300 +0200
@@ -1,7 +1,8 @@
 control ctrl() {
     bit<32> a;
+    bool hasReturned_0;
     apply {
-        bool hasReturned_0 = false;
+        hasReturned_0 = false;
         a = 32w0;
         if (a == 32w0) 
             hasReturned_0 = true;
