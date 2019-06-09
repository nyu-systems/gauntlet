--- before_pass
+++ after_pass
@@ -47,8 +47,8 @@ struct ingress_metadata_t {
     bit<1>  set_drop;
 }
 struct metadata {
-    @name("ingress_metadata") 
-    ingress_metadata_t local_metadata;
+    bit<16> _local_metadata_round0;
+    bit<1>  _local_metadata_set_drop1;
 }
 parser TopParser(packet_in b, out headers p, inout metadata meta, inout standard_metadata_t standard_metadata) {
     state start {
@@ -115,7 +115,7 @@ control egress(inout headers hdr, inout
     }
     @name("egress.drop_tbl") table drop_tbl_0 {
         key = {
-            meta.local_metadata.set_drop: exact @name("meta.ingress_metadata.set_drop") ;
+            meta._local_metadata_set_drop1: exact @name("meta.ingress_metadata.set_drop") ;
         }
         actions = {
             _drop();
@@ -131,7 +131,7 @@ control egress(inout headers hdr, inout
 control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
     @name("ingress.registerRound") register<bit<16>>(32w65536) registerRound_0;
     @name("ingress.read_round") action read_round() {
-        registerRound_0.read(meta.local_metadata.round, hdr.myhdr.inst);
+        registerRound_0.read(meta._local_metadata_round0, hdr.myhdr.inst);
     }
     @name("ingress.round_tbl") table round_tbl_0 {
         key = {
