--- dumps/p4_16_samples/issue907-bmv2.p4/pruned/issue907-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:31:13.229579900 +0200
+++ dumps/p4_16_samples/issue907-bmv2.p4/pruned/issue907-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:31:13.282596200 +0200
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
