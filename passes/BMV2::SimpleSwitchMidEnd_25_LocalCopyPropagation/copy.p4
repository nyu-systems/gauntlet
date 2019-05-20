--- dumps/p4_16_samples/copy.p4/pruned/copy-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:29:28.005085300 +0200
+++ dumps/p4_16_samples/copy.p4/pruned/copy-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:28.012076500 +0200
@@ -2,19 +2,14 @@ struct S {
     bit<32> x;
 }
 control c(inout bit<32> b) {
-    S s1;
-    S s2;
     @name("c.a") action a_0() {
         {
-            s2.x = 32w0;
         }
         {
-            s1.x = s2.x;
         }
         {
-            s2.x = s1.x;
         }
-        b = s2.x;
+        b = 32w0;
     }
     apply {
         a_0();
