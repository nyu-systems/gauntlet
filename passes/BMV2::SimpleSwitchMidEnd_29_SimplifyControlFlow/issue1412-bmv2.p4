--- dumps/pruned/issue1412-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:01.393266000 +0200
+++ dumps/pruned/issue1412-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:01.439437300 +0200
@@ -23,11 +23,7 @@ control EgressImpl(inout headers_t hdr,
     @name(".NoAction") action NoAction_0() {
     }
     @name("EgressImpl.set_true") action set_true_0() {
-        {
-            {
-                meta.cond = (meta.field == 8w0 ? true : meta.cond);
-            }
-        }
+        meta.cond = (meta.field == 8w0 ? true : meta.cond);
     }
     @name("EgressImpl.change_cond") table change_cond {
         key = {
