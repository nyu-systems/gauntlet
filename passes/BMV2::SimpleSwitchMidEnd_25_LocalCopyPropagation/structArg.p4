--- dumps/pruned/structArg-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:34:06.329672300 +0200
+++ dumps/pruned/structArg-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:34:06.333442200 +0200
@@ -2,10 +2,7 @@ struct S {
     bit<32> f;
 }
 control caller() {
-    S data;
     apply {
-        data.f = 32w0;
-        data.f = 32w0;
     }
 }
 control none();
