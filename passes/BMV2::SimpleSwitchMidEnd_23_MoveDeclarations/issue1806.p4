--- before_pass
+++ after_pass
@@ -14,11 +14,11 @@ parser prs(packet_in p, out Headers h) {
     }
 }
 control c(inout Headers h, inout standard_metadata_t sm) {
+    bit<10> key_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("c.do_act") action do_act_0() {
     }
-    bit<10> key_0;
     @name("c.tns") table tns {
         key = {
             key_0: exact @name("h.eth.tst[13:4]") ;
