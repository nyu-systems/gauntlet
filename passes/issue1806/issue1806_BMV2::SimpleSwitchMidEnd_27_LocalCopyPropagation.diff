--- before_pass
+++ after_pass
@@ -14,14 +14,13 @@ parser prs(packet_in p, out Headers h) {
     }
 }
 control c(inout Headers h, inout standard_metadata_t sm) {
-    bit<10> key_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("c.do_act") action do_act() {
     }
     @name("c.tns") table tns_0 {
         key = {
-            key_0: exact @name("h.eth.tst[13:4]") ;
+            h.eth.tst[13:4]: exact @name("h.eth.tst[13:4]") ;
         }
         actions = {
             do_act();
@@ -31,7 +30,6 @@ control c(inout Headers h, inout standar
     }
     apply {
         {
-            key_0 = h.eth.tst[13:4];
             tns_0.apply();
         }
     }
