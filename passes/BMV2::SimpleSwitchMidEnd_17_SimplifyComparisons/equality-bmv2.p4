--- dumps/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-06-08 18:31:34.653497200 +0200
+++ dumps/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:31:34.655334700 +0200
@@ -32,11 +32,11 @@ control ingress(inout headers hdr, inout
             hdr.same.same = hdr.same.same | 8w1;
         if (hdr.h.v == hdr.a[0].v) 
             hdr.same.same = hdr.same.same | 8w2;
-        if (hdr.h == hdr.a[0]) 
+        if (!hdr.h.isValid() && !hdr.a[0].isValid() || hdr.h.isValid() && hdr.a[0].isValid() && hdr.h.s == hdr.a[0].s && hdr.h.v == hdr.a[0].v) 
             hdr.same.same = hdr.same.same | 8w4;
         tmp[0] = hdr.h;
         tmp[1] = hdr.a[0];
-        if (tmp == hdr.a) 
+        if (true && (!tmp[0].isValid() && !hdr.a[0].isValid() || tmp[0].isValid() && hdr.a[0].isValid() && tmp[0].s == hdr.a[0].s && tmp[0].v == hdr.a[0].v) && (!tmp[1].isValid() && !hdr.a[1].isValid() || tmp[1].isValid() && hdr.a[1].isValid() && tmp[1].s == hdr.a[1].s && tmp[1].v == hdr.a[1].v)) 
             hdr.same.same = hdr.same.same | 8w8;
     }
 }
