--- before_pass
+++ after_pass
@@ -88,6 +88,10 @@ parser EgressParserImpl(packet_in buffer
     }
 }
 control ingress(inout headers hdr, inout metadata meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
+    psa_ingress_output_metadata_t meta_6;
+    PortId_t egress_port_0;
+    psa_ingress_output_metadata_t meta_7;
+    PortId_t egress_port_3;
     @name(".NoAction") action NoAction_0() {
     }
     @name(".NoAction") action NoAction_4() {
@@ -111,8 +115,8 @@ control ingress(inout headers hdr, inout
     }
     @name("ingress.do_L2_forward") action do_L2_forward_0(PortId_t egress_port) {
         {
-            psa_ingress_output_metadata_t meta_6 = ostd;
-            PortId_t egress_port_0 = egress_port;
+            meta_6 = ostd;
+            egress_port_0 = egress_port;
             meta_6.drop = false;
             meta_6.multicast_group = 10w0;
             meta_6.egress_port = egress_port_0;
@@ -121,8 +125,8 @@ control ingress(inout headers hdr, inout
     }
     @name("ingress.do_tst") action do_tst_0(PortId_t egress_port, bit<16> serEnumT) {
         {
-            psa_ingress_output_metadata_t meta_7 = ostd;
-            PortId_t egress_port_3 = egress_port;
+            meta_7 = ostd;
+            egress_port_3 = egress_port;
             meta_7.drop = false;
             meta_7.multicast_group = 10w0;
             meta_7.egress_port = egress_port_3;
