--- dumps/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:50.798174300 +0200
+++ dumps/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:50.800357800 +0200
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
