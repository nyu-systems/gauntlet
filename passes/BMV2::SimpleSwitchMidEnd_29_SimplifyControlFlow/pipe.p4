--- dumps/pruned/pipe-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:34:08.316533000 +0200
+++ dumps/pruned/pipe-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:34:08.370214200 +0200
@@ -62,27 +62,15 @@ control Q_pipe(inout TArg1 qArg1, inout
         const default_action = NoAction_0();
     }
     apply {
-        {
-            p1_tArg1_0.field1 = qArg1.field1;
-            p1_tArg1_0.drop = qArg1.drop;
-        }
-        {
-            p1_aArg2_0.field2 = qArg2.field2;
-        }
+        p1_tArg1_0.field1 = qArg1.field1;
+        p1_tArg1_0.drop = qArg1.drop;
+        p1_aArg2_0.field2 = qArg2.field2;
         p1_thost_T_0.apply();
-        {
-            qArg1.field1 = p1_tArg1_0.field1;
-        }
-        {
-            p1_tArg1_0.drop = qArg1.drop;
-        }
-        {
-            p1_aArg2_0.field2 = qArg2.field2;
-        }
+        qArg1.field1 = p1_tArg1_0.field1;
+        p1_tArg1_0.drop = qArg1.drop;
+        p1_aArg2_0.field2 = qArg2.field2;
         p1_thost_T_0.apply();
-        {
-            qArg1.field1 = p1_tArg1_0.field1;
-        }
+        qArg1.field1 = p1_tArg1_0.field1;
         p1_Tinner_0.apply();
     }
 }
