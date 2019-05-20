*** dumps/p4_16_samples/issue210.p4/pruned/issue210-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 16:59:01.764430700 +0200
--- dumps/p4_16_samples/issue210.p4/pruned/issue210-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 16:59:01.766919900 +0200
***************
*** 1,11 ****
  #include <core.p4>
  control Ing(out bit<32> a) {
      bool b;
      @name("Ing.cond") action cond_0() {
          {
-             bool cond;
              {
-                 bool pred;
                  cond = b;
                  pred = cond;
                  a = (pred ? 32w5 : a);
--- 1,11 ----
  #include <core.p4>
  control Ing(out bit<32> a) {
      bool b;
+     bool cond;
+     bool pred;
      @name("Ing.cond") action cond_0() {
          {
              {
                  cond = b;
                  pred = cond;
                  a = (pred ? 32w5 : a);
