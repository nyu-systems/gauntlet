--- dumps/p4_16_samples/def-use.p4/pruned/def-use-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:29:30.780175200 +0200
+++ dumps/p4_16_samples/def-use.p4/pruned/def-use-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:30.784818700 +0200
@@ -15,7 +15,6 @@ control IngressI(inout H hdr, inout M me
     }
 }
 control EgressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
-    bool hasReturned_0;
     @name("EgressI.a") action a_0() {
     }
     @name("EgressI.t") table t {
@@ -27,10 +26,8 @@ control EgressI(inout H hdr, inout M met
         default_action = a_0();
     }
     apply {
-        hasReturned_0 = false;
         switch (t.apply().action_run) {
             a_0: {
-                hasReturned_0 = true;
             }
             default: {
             }
