--- dumps/p4_16_samples/concat.p4/pruned/concat-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:24.328112700 +0200
+++ dumps/p4_16_samples/concat.p4/pruned/concat-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 17:29:24.337217300 +0200
@@ -2,7 +2,7 @@ control proto(out bit<32> x);
 package top(proto _c);
 control c(out bit<32> x) {
     apply {
-        x = 8w0xf ++ 16w0xf ++ 8w0xf + (16w0xf ++ (8w0xf ++ 8w0xf));
+        x = 32w0xf0f1e1e;
     }
 }
 top(c()) main;
