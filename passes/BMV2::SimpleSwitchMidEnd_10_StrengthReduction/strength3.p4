--- before_pass
+++ after_pass
@@ -14,7 +14,7 @@ struct Meta {
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
     @name("ingress.case0") action case0() {
-        h.h.c = (bit<8>)((16w0 ++ h.h.a)[15:0] ++ 16w0);
+        h.h.c = (bit<8>)(h.h.a[15:0] ++ 16w0);
     }
     @name("ingress.case1") action case1() {
         h.h.c = (bit<8>)h.h.a[15:0];
