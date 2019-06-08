--- dumps/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:31:50.808130200 +0200
+++ dumps/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:31:50.811350400 +0200
@@ -24,14 +24,6 @@ control ComputeChecksumI(inout H hdr, in
 }
 control IngressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
     apply {
-        {
-        }
-        {
-        }
-        {
-        }
-        {
-        }
     }
 }
 control EgressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
