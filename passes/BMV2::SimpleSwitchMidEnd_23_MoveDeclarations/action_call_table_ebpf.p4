--- dumps/p4_16_samples/action_call_table_ebpf.p4/pruned/action_call_table_ebpf-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 17:29:00.985247700 +0200
+++ dumps/p4_16_samples/action_call_table_ebpf.p4/pruned/action_call_table_ebpf-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:29:00.987349100 +0200
@@ -8,11 +8,13 @@ parser prs(packet_in p, out Headers_t he
     }
 }
 control pipe(inout Headers_t headers, out bool pass) {
+    bool cond;
+    bool pred;
+    bool cond_0;
+    bool pred_0;
     @name("pipe.Reject") action Reject_0(bit<8> rej, bit<8> bar) {
         {
-            bool cond;
             {
-                bool pred;
                 cond = rej == 8w0;
                 pred = cond;
                 pass = (pred ? true : pass);
@@ -22,9 +24,7 @@ control pipe(inout Headers_t headers, ou
             }
         }
         {
-            bool cond_0;
             {
-                bool pred_0;
                 cond_0 = bar == 8w0;
                 pred_0 = cond_0;
                 pass = (pred_0 ? false : pass);
