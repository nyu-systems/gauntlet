--- dumps/pruned/concat-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:25.754179000 +0200
+++ dumps/pruned/concat-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:25.756902100 +0200
@@ -1,12 +1,8 @@
 control proto(out bit<32> x);
 package top(proto _c);
 control c(out bit<32> x) {
-    bit<8> a;
-    bit<16> b;
     apply {
-        a = 8w0xf;
-        b = 16w0xf;
-        x = a ++ b ++ a + (b ++ (a ++ a));
+        x = 8w0xf ++ 16w0xf ++ 8w0xf + (16w0xf ++ (8w0xf ++ 8w0xf));
     }
 }
 top(c()) main;
