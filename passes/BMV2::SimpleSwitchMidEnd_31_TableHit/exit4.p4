--- dumps/pruned/exit4-BMV2::SimpleSwitchMidEnd_30_CompileTimeOperations.p4	2019-06-08 18:31:37.247174400 +0200
+++ dumps/pruned/exit4-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-06-08 18:31:37.249232800 +0200
@@ -10,7 +10,10 @@ control ctrl() {
         default_action = e_0();
     }
     apply {
-        tmp_0 = t.apply().hit;
+        if (t.apply().hit) 
+            tmp_0 = true;
+        else 
+            tmp_0 = false;
         if (tmp_0) 
             t.apply();
         else 
