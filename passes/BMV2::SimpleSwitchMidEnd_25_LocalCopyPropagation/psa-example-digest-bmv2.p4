--- dumps/pruned/psa-example-digest-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:33:17.883142400 +0200
+++ dumps/pruned/psa-example-digest-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:33:17.887189100 +0200
@@ -120,10 +120,6 @@ parser EgressParserImpl(packet_in buffer
     }
 }
 control ingress(inout headers hdr, inout metadata meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
-    psa_ingress_output_metadata_t meta_6;
-    PortId_t egress_port_0;
-    psa_ingress_output_metadata_t meta_7;
-    PortId_t egress_port_3;
     @name(".NoAction") action NoAction_0() {
     }
     @name(".NoAction") action NoAction_4() {
@@ -148,52 +144,22 @@ control ingress(inout headers hdr, inout
     @name("ingress.do_L2_forward") action do_L2_forward_0(PortId_t egress_port) {
         {
             {
-                meta_6.class_of_service = ostd.class_of_service;
-                meta_6.clone = ostd.clone;
-                meta_6.clone_session_id = ostd.clone_session_id;
-                meta_6.drop = ostd.drop;
-                meta_6.resubmit = ostd.resubmit;
-                meta_6.multicast_group = ostd.multicast_group;
-                meta_6.egress_port = ostd.egress_port;
             }
-            egress_port_0 = egress_port;
-            meta_6.drop = false;
-            meta_6.multicast_group = 10w0;
-            meta_6.egress_port = egress_port_0;
             {
-                ostd.class_of_service = meta_6.class_of_service;
-                ostd.clone = meta_6.clone;
-                ostd.clone_session_id = meta_6.clone_session_id;
-                ostd.drop = meta_6.drop;
-                ostd.resubmit = meta_6.resubmit;
-                ostd.multicast_group = meta_6.multicast_group;
-                ostd.egress_port = meta_6.egress_port;
+                ostd.drop = false;
+                ostd.multicast_group = 10w0;
+                ostd.egress_port = egress_port;
             }
         }
     }
     @name("ingress.do_tst") action do_tst_0(PortId_t egress_port, bit<16> serEnumT) {
         {
             {
-                meta_7.class_of_service = ostd.class_of_service;
-                meta_7.clone = ostd.clone;
-                meta_7.clone_session_id = ostd.clone_session_id;
-                meta_7.drop = ostd.drop;
-                meta_7.resubmit = ostd.resubmit;
-                meta_7.multicast_group = ostd.multicast_group;
-                meta_7.egress_port = ostd.egress_port;
             }
-            egress_port_3 = egress_port;
-            meta_7.drop = false;
-            meta_7.multicast_group = 10w0;
-            meta_7.egress_port = egress_port_3;
             {
-                ostd.class_of_service = meta_7.class_of_service;
-                ostd.clone = meta_7.clone;
-                ostd.clone_session_id = meta_7.clone_session_id;
-                ostd.drop = meta_7.drop;
-                ostd.resubmit = meta_7.resubmit;
-                ostd.multicast_group = meta_7.multicast_group;
-                ostd.egress_port = meta_7.egress_port;
+                ostd.drop = false;
+                ostd.multicast_group = 10w0;
+                ostd.egress_port = egress_port;
             }
         }
     }
