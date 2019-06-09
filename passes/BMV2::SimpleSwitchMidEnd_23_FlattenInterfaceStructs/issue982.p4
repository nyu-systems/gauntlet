--- before_pass
+++ after_pass
@@ -209,10 +209,10 @@ struct fwd_metadata_t {
     bit<32> outport;
 }
 struct metadata {
-    fwd_metadata_t fwd_metadata;
-    bit<3>         custom_clone_id;
-    clone_0_t      clone_0;
-    clone_1_t      clone_1;
+    bit<32>   _fwd_metadata_outport0;
+    bit<3>    _custom_clone_id1;
+    clone_0_t _clone_02;
+    clone_1_t _clone_13;
 }
 struct headers {
     ethernet_t ethernet;
@@ -249,13 +249,13 @@ parser EgressParserImpl(packet_in buffer
         }
     }
     state CloneParser_parse_clone_header {
-        user_meta.custom_clone_id = istd.clone_metadata.type;
-        user_meta.clone_0 = istd.clone_metadata.data.h0;
+        user_meta._custom_clone_id1 = istd.clone_metadata.type;
+        user_meta._clone_02 = istd.clone_metadata.data.h0;
         transition parse_clone_header_2;
     }
     state CloneParser_parse_clone_header_0 {
-        user_meta.custom_clone_id = istd.clone_metadata.type;
-        user_meta.clone_1 = istd.clone_metadata.data.h1;
+        user_meta._custom_clone_id1 = istd.clone_metadata.type;
+        user_meta._clone_13 = istd.clone_metadata.data.h1;
         transition parse_clone_header_2;
     }
     state parse_clone_header_2 {
@@ -266,14 +266,14 @@ control egress(inout headers hdr, inout
     @name(".NoAction") action NoAction_0() {
     }
     @name("egress.process_clone_h0") action process_clone_h0() {
-        user_meta.fwd_metadata.outport = (bit<32>)user_meta.clone_0.data;
+        user_meta._fwd_metadata_outport0 = (bit<32>)user_meta._clone_02.data;
     }
     @name("egress.process_clone_h1") action process_clone_h1() {
-        user_meta.fwd_metadata.outport = user_meta.clone_1.data;
+        user_meta._fwd_metadata_outport0 = user_meta._clone_13.data;
     }
     @name("egress.t") table t_0 {
         key = {
-            user_meta.custom_clone_id: exact @name("user_meta.custom_clone_id") ;
+            user_meta._custom_clone_id1: exact @name("user_meta.custom_clone_id") ;
         }
         actions = {
             process_clone_h0();
@@ -310,11 +310,11 @@ control ingress(inout headers hdr, inout
     @name("ingress.do_clone") action do_clone(PortId_t port) {
         ostd.clone = true;
         ostd.clone_port = port;
-        user_meta.custom_clone_id = 3w1;
+        user_meta._custom_clone_id1 = 3w1;
     }
     @name("ingress.t") table t_1 {
         key = {
-            user_meta.fwd_metadata.outport: exact @name("user_meta.fwd_metadata.outport") ;
+            user_meta._fwd_metadata_outport0: exact @name("user_meta.fwd_metadata.outport") ;
         }
         actions = {
             do_clone();
@@ -335,7 +335,7 @@ control IngressDeparserImpl(packet_out p
             clone_md_0_data.h1.data = 32w0;
         }
         clone_md_0_type = 3w0;
-        if (meta.custom_clone_id == 3w1) {
+        if (meta._custom_clone_id1 == 3w1) {
             ostd.clone_metadata.type = clone_md_0_type;
             {
                 ostd.clone_metadata.data.h0 = clone_md_0_data.h0;
