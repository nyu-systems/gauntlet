--- dumps/p4_16_samples/newtype.p4/pruned/newtype-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:31:27.120133400 +0200
+++ dumps/p4_16_samples/newtype.p4/pruned/newtype-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:31:27.171983600 +0200
@@ -24,7 +24,6 @@ control c(out B32 x) {
     apply {
         k = 32w0;
         x = 32w0;
-        ;
         t.apply();
         x = 32w3;
     }
