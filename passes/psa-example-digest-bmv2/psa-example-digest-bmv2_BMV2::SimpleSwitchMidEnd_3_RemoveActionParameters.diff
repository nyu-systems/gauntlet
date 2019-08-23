--- before_pass
+++ after_pass
@@ -78,6 +78,10 @@ parser EgressParserImpl(packet_in buffer
     }
 }
 control ingress(inout headers hdr, inout metadata meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
+    psa_ingress_output_metadata_t meta_1;
+    PortId_t egress_port_1;
+    psa_ingress_output_metadata_t meta_2;
+    PortId_t egress_port_2;
     @name(".NoAction") action NoAction_0() {
     }
     @name(".NoAction") action NoAction_4() {
@@ -101,8 +105,8 @@ control ingress(inout headers hdr, inout
     }
     @name("ingress.do_L2_forward") action do_L2_forward(PortId_t egress_port) {
         {
-            psa_ingress_output_metadata_t meta_1 = ostd;
-            PortId_t egress_port_1 = egress_port;
+            meta_1 = ostd;
+            egress_port_1 = egress_port;
             meta_1.drop = false;
             meta_1.multicast_group = 32w0;
             meta_1.egress_port = egress_port_1;
@@ -111,8 +115,8 @@ control ingress(inout headers hdr, inout
     }
     @name("ingress.do_tst") action do_tst(PortId_t egress_port, bit<16> serEnumT) {
         {
-            psa_ingress_output_metadata_t meta_2 = ostd;
-            PortId_t egress_port_2 = egress_port;
+            meta_2 = ostd;
+            egress_port_2 = egress_port;
             meta_2.drop = false;
             meta_2.multicast_group = 32w0;
             meta_2.egress_port = egress_port_2;
