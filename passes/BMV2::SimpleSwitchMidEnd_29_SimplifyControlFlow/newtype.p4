--- dumps/pruned/newtype-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:33:00.625053400 +0200
+++ dumps/pruned/newtype-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:33:00.663109200 +0200
@@ -24,7 +24,6 @@ control c(out B32 x) {
     apply {
         k = 32w0;
         x = 32w0;
-        ;
         t.apply();
         x = 32w3;
     }
