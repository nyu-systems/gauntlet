--- before_pass
+++ after_pass
@@ -40,6 +40,8 @@ parser prs(packet_in p, out Headers_t he
 }
 control pipe(inout Headers_t headers, out bool pass) {
     bool tmp_0;
+    bit<32> key_0;
+    bit<32> key_1;
     @name("pipe.invalidate") action invalidate_0() {
         headers.ipv4.setInvalid();
         headers.ethernet.setInvalid();
@@ -48,8 +50,6 @@ control pipe(inout Headers_t headers, ou
     @name("pipe.drop") action drop_0() {
         pass = false;
     }
-    bit<32> key_0;
-    bit<32> key_1;
     @name("pipe.t") table t {
         key = {
             key_0                   : exact @name(" headers.ipv4.srcAddr") ;
