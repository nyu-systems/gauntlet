--- dumps/pruned/pipe-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:34:08.278533400 +0200
+++ dumps/pruned/pipe-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:34:08.283331600 +0200
@@ -64,14 +64,30 @@ control Q_pipe(inout TArg1 qArg1, inout
         const default_action = NoAction_0();
     }
     apply {
-        p1_tArg1_0 = qArg1;
-        p1_aArg2_0 = qArg2;
+        {
+            p1_tArg1_0.field1 = qArg1.field1;
+            p1_tArg1_0.drop = qArg1.drop;
+        }
+        {
+            p1_aArg2_0.field2 = qArg2.field2;
+        }
         p1_thost_T_0.apply();
-        qArg1 = p1_tArg1_0;
-        p1_tArg1_0 = qArg1;
-        p1_aArg2_0 = qArg2;
+        {
+            qArg1.field1 = p1_tArg1_0.field1;
+            qArg1.drop = p1_tArg1_0.drop;
+        }
+        {
+            p1_tArg1_0.field1 = qArg1.field1;
+            p1_tArg1_0.drop = qArg1.drop;
+        }
+        {
+            p1_aArg2_0.field2 = qArg2.field2;
+        }
         p1_thost_T_0.apply();
-        qArg1 = p1_tArg1_0;
+        {
+            qArg1.field1 = p1_tArg1_0.field1;
+            qArg1.drop = p1_tArg1_0.drop;
+        }
         p1_Tinner_0.apply();
     }
 }
