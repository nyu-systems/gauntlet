--- dumps/p4_16_samples/exit4.p4/pruned/exit4-BMV2::SimpleSwitchMidEnd_30_CompileTimeOperations.p4	2019-05-20 17:29:42.937625000 +0200
+++ dumps/p4_16_samples/exit4.p4/pruned/exit4-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-05-20 17:29:42.940970800 +0200
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
