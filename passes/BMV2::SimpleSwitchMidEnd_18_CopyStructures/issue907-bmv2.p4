--- dumps/pruned/issue907-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:32:48.143179500 +0200
+++ dumps/pruned/issue907-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:32:48.145168600 +0200
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
