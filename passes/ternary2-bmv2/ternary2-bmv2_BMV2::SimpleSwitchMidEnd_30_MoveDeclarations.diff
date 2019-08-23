--- before_pass
+++ after_pass
@@ -40,6 +40,7 @@ control update(inout packet_t h, inout M
     }
 }
 control ingress(inout packet_t hdrs, inout Meta m, inout standard_metadata_t meta) {
+    bit<16> key_0;
     @name("ingress.setb1") action setb1(bit<9> port, bit<8> val) {
         hdrs.data.b1 = val;
         meta.egress_spec = port;
@@ -85,7 +86,6 @@ control ingress(inout packet_t hdrs, ino
         }
         default_action = noop();
     }
-    bit<16> key_0;
     @name("ingress.ex1") table ex1_0 {
         key = {
             key_0: ternary @name("hdrs.extra[0].h") ;
