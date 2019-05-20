--- dumps/p4_16_samples/issue907-bmv2.p4/pruned/issue907-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:31:13.195771600 +0200
+++ dumps/p4_16_samples/issue907-bmv2.p4/pruned/issue907-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:31:13.198505800 +0200
@@ -16,7 +16,9 @@ control Ing(inout Headers headers, inout
     S s;
     @name("Ing.r") register<S>(32w100) r;
     apply {
-        s = { 32w0 };
+        {
+            s.f = 32w0;
+        }
         r.write(32w0, s);
     }
 }
