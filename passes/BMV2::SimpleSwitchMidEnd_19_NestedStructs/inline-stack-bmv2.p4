--- dumps/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:31:50.785754600 +0200
+++ dumps/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-06-08 18:31:50.787828500 +0200
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
