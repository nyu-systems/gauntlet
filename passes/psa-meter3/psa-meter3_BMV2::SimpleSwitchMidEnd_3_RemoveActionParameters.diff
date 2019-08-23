--- before_pass
+++ after_pass
@@ -20,10 +20,10 @@ parser MyEP(packet_in buffer, out EMPTY
     }
 }
 control MyIC(inout ethernet_t a, inout EMPTY b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
-    @name(".NoAction") action NoAction_0() {
-    }
     PSA_MeterColor_t tmp;
     bool tmp_0;
+    @name(".NoAction") action NoAction_0() {
+    }
     @name("MyIC.meter0") Meter<bit<12>>(32w1024, PSA_MeterType_t.PACKETS) meter0_0;
     @name("MyIC.tbl") table tbl_0 {
         key = {
