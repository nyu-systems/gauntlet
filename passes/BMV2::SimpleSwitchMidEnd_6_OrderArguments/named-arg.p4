--- dumps/pruned/named-arg-BMV2::SimpleSwitchMidEnd_5_VisitFunctor.p4	2019-06-08 18:32:58.677267400 +0200
+++ dumps/pruned/named-arg-BMV2::SimpleSwitchMidEnd_6_OrderArguments.p4	2019-06-08 18:32:58.680598300 +0200
@@ -5,7 +5,7 @@ control c() {
     apply {
         xv = 16w0;
         b = true;
-        f(y = b, x = xv);
+        f(x = xv, y = b);
     }
 }
 control empty();
