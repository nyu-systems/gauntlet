--- before_pass
+++ after_pass
@@ -17,9 +17,10 @@ struct meta_t {
 control MyC(inout hdr_t hdr, inout meta_t meta, in intrinsic_metadata_t intr_md) {
     @name(".NoAction") action NoAction_0() {
     }
+    bit<8> key_0;
     @name("MyC.c2.a") table c2_a {
         key = {
-            meta_t {f0 = 8w0,f1 = 8w0,f2 = 8w0}.f0: exact @name("meta.f0") ;
+            key_0: exact @name("meta.f0") ;
         }
         actions = {
             NoAction_0();
@@ -27,7 +28,10 @@ control MyC(inout hdr_t hdr, inout meta_
         default_action = NoAction_0();
     }
     apply {
-        c2_a.apply();
+        {
+            key_0 = meta_t {f0 = 8w0,f1 = 8w0,f2 = 8w0}.f0;
+            c2_a.apply();
+        }
     }
 }
 P<hdr_t, meta_t>(MyC()) main;
