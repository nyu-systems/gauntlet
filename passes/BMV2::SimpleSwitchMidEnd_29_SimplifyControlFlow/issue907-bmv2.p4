--- dumps/pruned/issue907-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:48.167089900 +0200
+++ dumps/pruned/issue907-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:48.212769000 +0200
@@ -16,9 +16,7 @@ control Ing(inout Headers headers, inout
     S s;
     @name("Ing.r") register<S>(32w100) r;
     apply {
-        {
-            s.f = 32w0;
-        }
+        s.f = 32w0;
         r.write(32w0, s);
     }
 }
