--- before_pass
+++ after_pass
@@ -7,7 +7,7 @@ struct some_meta_t {
 struct H {
 }
 struct M {
-    some_meta_t some_meta;
+    bool _some_meta_flag0;
 }
 control DeparserI(packet_out packet, in H hdr) {
     apply {
@@ -28,7 +28,7 @@ control ComputeChecksumI(inout H hdr, in
 }
 control IngressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
     apply {
-        meta.some_meta.flag = true;
+        meta._some_meta_flag0 = true;
     }
 }
 control EgressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
