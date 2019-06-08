--- dumps/pruned/stack2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:34:02.146209600 +0200
+++ dumps/pruned/stack2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:34:02.148720700 +0200
@@ -2,10 +2,8 @@
 header h {
 }
 control c(out bit<32> x) {
-    bit<32> sz;
     apply {
-        sz = 32w4;
-        x = sz;
+        x = 32w4;
     }
 }
 control Simpler(out bit<32> x);
