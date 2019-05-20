--- dumps/p4_16_samples/named-arg.p4/pruned/named-arg-BMV2::SimpleSwitchMidEnd_5_VisitFunctor.p4	2019-05-20 17:31:25.039662300 +0200
+++ dumps/p4_16_samples/named-arg.p4/pruned/named-arg-BMV2::SimpleSwitchMidEnd_6_OrderArguments.p4	2019-05-20 17:31:25.045515700 +0200
@@ -5,7 +5,7 @@ control c() {
     apply {
         xv = 16w0;
         b = true;
-        f(y = b, x = xv);
+        f(x = xv, y = b);
     }
 }
 control empty();
