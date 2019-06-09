--- before_pass
+++ after_pass
@@ -7,19 +7,15 @@ control t(inout bit<32> b) {
     @name("t.c1.x") X() c1_x = {
         void a(inout bit<32> arg) {
             bit<32> c1_tmp;
-            bit<32> c1_tmp_0;
             c1_tmp = this.b();
-            c1_tmp_0 = arg + c1_tmp;
-            arg = c1_tmp_0;
+            arg = arg + c1_tmp;
         }
     };
     @name("t.c2.x") X() c2_x = {
         void a(inout bit<32> arg) {
             bit<32> c2_tmp;
-            bit<32> c2_tmp_0;
             c2_tmp = this.b();
-            c2_tmp_0 = arg + c2_tmp;
-            arg = c2_tmp_0;
+            arg = arg + c2_tmp;
         }
     };
     apply {
