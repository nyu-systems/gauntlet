--- dumps/p4_16_samples/inline-stack-bmv2.p4/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:30:03.755144000 +0200
+++ dumps/p4_16_samples/inline-stack-bmv2.p4/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:30:03.759657300 +0200
@@ -23,19 +23,14 @@ control ComputeChecksumI(inout H hdr, in
     }
 }
 control IngressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
-    h_t[1] hdr_1_stack;
     apply {
         {
-            hdr_1_stack = hdr.stack;
         }
         {
-            hdr.stack = hdr_1_stack;
         }
         {
-            hdr_1_stack = hdr.stack;
         }
         {
-            hdr.stack = hdr_1_stack;
         }
     }
 }
