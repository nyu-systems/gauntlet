--- before_pass
+++ after_pass
@@ -29,7 +29,7 @@ control ingress(inout headers hdr, inout
         hdr.same.same = 8w0;
         stdmeta.egress_spec = 9w0;
         if (hdr.h.s == hdr.a[0].s) 
-            hdr.same.same = hdr.same.same | 8w1;
+            hdr.same.same = 8w0 | 8w1;
         if (hdr.h.v == hdr.a[0].v) 
             hdr.same.same = hdr.same.same | 8w2;
         if (!hdr.h.isValid() && !hdr.a[0].isValid() || hdr.h.isValid() && hdr.a[0].isValid() && hdr.h.s == hdr.a[0].s && hdr.h.v == hdr.a[0].v) 
