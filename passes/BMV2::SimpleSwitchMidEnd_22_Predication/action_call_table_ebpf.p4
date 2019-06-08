--- dumps/pruned/action_call_table_ebpf-BMV2::SimpleSwitchMidEnd_21_RemoveSelectBooleans.p4	2019-06-08 18:31:00.732347400 +0200
+++ dumps/pruned/action_call_table_ebpf-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-06-08 18:31:00.734562500 +0200
@@ -9,12 +9,27 @@ parser prs(packet_in p, out Headers_t he
 }
 control pipe(inout Headers_t headers, out bool pass) {
     @name("pipe.Reject") action Reject_0(bit<8> rej, bit<8> bar) {
-        if (rej == 8w0) 
-            pass = true;
-        else 
-            pass = false;
-        if (bar == 8w0) 
-            pass = false;
+        {
+            bool cond;
+            {
+                bool pred;
+                cond = rej == 8w0;
+                pred = cond;
+                pass = (pred ? true : pass);
+                cond = !cond;
+                pred = cond;
+                pass = (pred ? false : pass);
+            }
+        }
+        {
+            bool cond_0;
+            {
+                bool pred_0;
+                cond_0 = bar == 8w0;
+                pred_0 = cond_0;
+                pass = (pred_0 ? false : pass);
+            }
+        }
     }
     @name("pipe.t") table t {
         actions = {
