--- before_pass
+++ after_pass
@@ -15,9 +15,9 @@ struct meta_t {
     bit<8> f2;
 }
 control MyC(inout hdr_t hdr, inout meta_t meta, in intrinsic_metadata_t intr_md) {
+    bit<8> key_0;
     @name(".NoAction") action NoAction_0() {
     }
-    bit<8> key_0;
     @name("MyC.c2.a") table c2_a {
         key = {
             key_0: exact @name("meta.f0") ;
