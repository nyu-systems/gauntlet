--- before_pass
+++ after_pass
@@ -22,7 +22,7 @@ parser MyEP(packet_in buffer, out EMPTY
 control MyIC(inout ethernet_t a, inout EMPTY b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
     @name(".NoAction") action NoAction_0() {
     }
-    @name("MyIC.counter0") DirectCounter<bit<12>>(PSA_CounterType_t.PACKETS) counter0_0;
+    @name("MyIC.counter0") DirectCounter<bit<12>>(32w0) counter0_0;
     @name("MyIC.tbl") table tbl_0 {
         key = {
             a.srcAddr: exact @name("a.srcAddr") ;
