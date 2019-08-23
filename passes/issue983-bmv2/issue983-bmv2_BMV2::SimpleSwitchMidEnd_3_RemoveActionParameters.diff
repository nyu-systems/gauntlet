--- before_pass
+++ after_pass
@@ -31,11 +31,11 @@ parser IngressParserImpl(packet_in buffe
     }
 }
 control ingress(inout headers hdr, inout metadata user_meta, inout standard_metadata_t standard_metadata) {
-    @name(".NoAction") action NoAction_0() {
-    }
     bit<16> tmp_0;
     bit<32> x1_0;
     bit<16> x2_0;
+    @name(".NoAction") action NoAction_0() {
+    }
     @name("ingress.debug_table_cksum1") table debug_table_cksum1_0 {
         key = {
             hdr.ethernet.srcAddr            : exact @name("hdr.ethernet.srcAddr") ;
