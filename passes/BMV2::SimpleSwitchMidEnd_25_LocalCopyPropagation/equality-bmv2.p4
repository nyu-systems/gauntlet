--- dumps/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:34.667725100 +0200
+++ dumps/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:34.669293200 +0200
@@ -29,7 +29,7 @@ control ingress(inout headers hdr, inout
         hdr.same.same = 8w0;
         stdmeta.egress_spec = 9w0;
         if (hdr.h.s == hdr.a[0].s) 
-            hdr.same.same = hdr.same.same | 8w1;
+            hdr.same.same = 8w0 | 8w1;
         if (hdr.h.v == hdr.a[0].v) 
             hdr.same.same = hdr.same.same | 8w2;
         if (!hdr.h.isValid() && !hdr.a[0].isValid() || hdr.h.isValid() && hdr.a[0].isValid() && hdr.h.s == hdr.a[0].s && hdr.h.v == hdr.a[0].v) 
