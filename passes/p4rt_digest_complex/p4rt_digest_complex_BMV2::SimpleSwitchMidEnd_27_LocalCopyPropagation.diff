--- before_pass
+++ after_pass
@@ -39,15 +39,9 @@ struct digest_t {
     PortId_t port;
 }
 control MyID(packet_out buffer, out EMPTY a, out EMPTY b, out EMPTY c, inout headers hdr, in EMPTY e, in psa_ingress_output_metadata_t f) {
-    h_t tmp_h;
-    bit<32> tmp_port;
     @name("MyID.digest") Digest<digest_t>() digest_0;
     apply {
-        {
-            tmp_h = hdr.h;
-            tmp_port = f.egress_port;
-        }
-        digest_0.pack({ tmp_h, tmp_port });
+        digest_0.pack({ hdr.h, f.egress_port });
     }
 }
 control MyED(packet_out buffer, out EMPTY a, out EMPTY b, inout EMPTY c, in EMPTY d, in psa_egress_output_metadata_t e, in psa_egress_deparser_input_metadata_t f) {
