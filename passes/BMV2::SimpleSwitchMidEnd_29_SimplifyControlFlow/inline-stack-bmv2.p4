--- before_pass
+++ after_pass
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
