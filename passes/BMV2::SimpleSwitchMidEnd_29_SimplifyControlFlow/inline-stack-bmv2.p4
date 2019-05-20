--- dumps/p4_16_samples/inline-stack-bmv2.p4/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:30:03.768420300 +0200
+++ dumps/p4_16_samples/inline-stack-bmv2.p4/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:30:03.770895500 +0200
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
