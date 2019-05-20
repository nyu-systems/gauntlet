*** dumps/p4_16_samples/action_call_table_ebpf.p4/pruned/action_call_table_ebpf-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 16:57:46.507692400 +0200
--- dumps/p4_16_samples/action_call_table_ebpf.p4/pruned/action_call_table_ebpf-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 16:57:46.513216200 +0200
*************** parser prs(packet_in p, out Headers_t he
*** 8,18 ****
      }
  }
  control pipe(inout Headers_t headers, out bool pass) {
      @name("pipe.Reject") action Reject_0(bit<8> rej, bit<8> bar) {
          {
-             bool cond;
              {
-                 bool pred;
                  cond = rej == 8w0;
                  pred = cond;
                  pass = (pred ? true : pass);
--- 8,20 ----
      }
  }
  control pipe(inout Headers_t headers, out bool pass) {
+     bool cond;
+     bool pred;
+     bool cond_0;
+     bool pred_0;
      @name("pipe.Reject") action Reject_0(bit<8> rej, bit<8> bar) {
          {
              {
                  cond = rej == 8w0;
                  pred = cond;
                  pass = (pred ? true : pass);
*************** control pipe(inout Headers_t headers, ou
*** 22,30 ****
              }
          }
          {
-             bool cond_0;
              {
-                 bool pred_0;
                  cond_0 = bar == 8w0;
                  pred_0 = cond_0;
                  pass = (pred_0 ? false : pass);
--- 24,30 ----
