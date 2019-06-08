--- before_pass
+++ after_pass
@@ -7,7 +7,6 @@ control A(inout hdr _hdr) {
         _hdr_1 = _hdr;
         _hdr_1.g = 1w1;
         _hdr = _hdr_1;
-        _hdr_1 = _hdr;
         _hdr_1.g = 1w1;
         _hdr = _hdr_1;
     }
