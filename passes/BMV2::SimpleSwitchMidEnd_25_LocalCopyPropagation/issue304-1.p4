--- dumps/pruned/issue304-1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:32:21.208126100 +0200
+++ dumps/pruned/issue304-1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:21.212480600 +0200
@@ -7,19 +7,15 @@ control t(inout bit<32> b) {
     @name("t.c1.x") X() c1_x_0 = {
         void a(inout bit<32> arg) {
             bit<32> c1_tmp_1;
-            bit<32> c1_tmp_2;
             c1_tmp_1 = this.b();
-            c1_tmp_2 = arg + c1_tmp_1;
-            arg = c1_tmp_2;
+            arg = arg + c1_tmp_1;
         }
     };
     @name("t.c2.x") X() c2_x_0 = {
         void a(inout bit<32> arg) {
             bit<32> c2_tmp_1;
-            bit<32> c2_tmp_2;
             c2_tmp_1 = this.b();
-            c2_tmp_2 = arg + c2_tmp_1;
-            arg = c2_tmp_2;
+            arg = arg + c2_tmp_1;
         }
     };
     apply {
