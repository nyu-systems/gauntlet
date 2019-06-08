--- dumps/pruned/issue1412-bmv2-BMV2::SimpleSwitchMidEnd_21_RemoveSelectBooleans.p4	2019-06-08 18:32:01.378308800 +0200
+++ dumps/pruned/issue1412-bmv2-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-06-08 18:32:01.380287800 +0200
@@ -23,8 +23,15 @@ control EgressImpl(inout headers_t hdr,
     @name(".NoAction") action NoAction_0() {
     }
     @name("EgressImpl.set_true") action set_true_0() {
-        if (meta.field == 8w0) 
-            meta.cond = true;
+        {
+            bool cond_0;
+            {
+                bool pred;
+                cond_0 = meta.field == 8w0;
+                pred = cond_0;
+                meta.cond = (pred ? true : meta.cond);
+            }
+        }
     }
     @name("EgressImpl.change_cond") table change_cond {
         key = {
