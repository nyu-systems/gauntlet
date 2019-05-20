--- dumps/p4_16_samples/issue1334.p4/pruned/issue1334-BMV2::SimpleSwitchMidEnd_5_VisitFunctor.p4	2019-05-20 17:30:13.209804700 +0200
+++ dumps/p4_16_samples/issue1334.p4/pruned/issue1334-BMV2::SimpleSwitchMidEnd_6_OrderArguments.p4	2019-05-20 17:30:13.212422700 +0200
@@ -17,12 +17,12 @@ control c() {
         f(a = 32w2);
         f(b = 16w1);
         f(a = 32w1, b = 16w2);
-        f(b = 16w2, a = 32w1);
+        f(a = 32w1, b = 16w2);
         o.f();
         o.f(a = 32w2);
         o.f(b = 16w1);
         o.f(a = 32w1, b = 16w2);
-        o.f(b = 16w2, a = 32w1);
+        o.f(a = 32w1, b = 16w2);
         z = 32w4294967294;
     }
 }
