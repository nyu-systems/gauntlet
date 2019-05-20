--- dumps/p4_16_samples/inline-stack-bmv2.p4/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:30:03.737724700 +0200
+++ dumps/p4_16_samples/inline-stack-bmv2.p4/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-05-20 17:30:03.740791700 +0200
@@ -23,19 +23,19 @@ control ComputeChecksumI(inout H hdr, in
     }
 }
 control IngressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
-    H hdr_1;
+    h_t[1] hdr_1_stack;
     apply {
         {
-            hdr_1.stack = hdr.stack;
+            hdr_1_stack = hdr.stack;
         }
         {
-            hdr.stack = hdr_1.stack;
+            hdr.stack = hdr_1_stack;
         }
         {
-            hdr_1.stack = hdr.stack;
+            hdr_1_stack = hdr.stack;
         }
         {
-            hdr.stack = hdr_1.stack;
+            hdr.stack = hdr_1_stack;
         }
     }
 }
