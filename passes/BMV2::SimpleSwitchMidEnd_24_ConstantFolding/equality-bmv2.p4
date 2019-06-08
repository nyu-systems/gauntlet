--- before_pass
+++ after_pass
@@ -36,7 +36,7 @@ control ingress(inout headers hdr, inout
             hdr.same.same = hdr.same.same | 8w4;
         tmp[0] = hdr.h;
         tmp[1] = hdr.a[0];
-        if (true && (!tmp[0].isValid() && !hdr.a[0].isValid() || tmp[0].isValid() && hdr.a[0].isValid() && tmp[0].s == hdr.a[0].s && tmp[0].v == hdr.a[0].v) && (!tmp[1].isValid() && !hdr.a[1].isValid() || tmp[1].isValid() && hdr.a[1].isValid() && tmp[1].s == hdr.a[1].s && tmp[1].v == hdr.a[1].v)) 
+        if ((!tmp[0].isValid() && !hdr.a[0].isValid() || tmp[0].isValid() && hdr.a[0].isValid() && tmp[0].s == hdr.a[0].s && tmp[0].v == hdr.a[0].v) && (!tmp[1].isValid() && !hdr.a[1].isValid() || tmp[1].isValid() && hdr.a[1].isValid() && tmp[1].s == hdr.a[1].s && tmp[1].v == hdr.a[1].v)) 
             hdr.same.same = hdr.same.same | 8w8;
     }
 }
