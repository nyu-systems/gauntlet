--- dumps/p4_16_samples/structArg.p4/pruned/structArg-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:32:17.295824900 +0200
+++ dumps/p4_16_samples/structArg.p4/pruned/structArg-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:32:17.298709300 +0200
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
