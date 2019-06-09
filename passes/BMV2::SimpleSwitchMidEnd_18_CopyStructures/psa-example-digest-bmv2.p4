--- before_pass
+++ after_pass
@@ -99,22 +99,54 @@ control ingress(inout headers hdr, inout
     }
     @name("ingress.do_L2_forward") action do_L2_forward(PortId_t egress_port) {
         {
-            meta_1 = ostd;
+            {
+                meta_1.class_of_service = ostd.class_of_service;
+                meta_1.clone = ostd.clone;
+                meta_1.clone_session_id = ostd.clone_session_id;
+                meta_1.drop = ostd.drop;
+                meta_1.resubmit = ostd.resubmit;
+                meta_1.multicast_group = ostd.multicast_group;
+                meta_1.egress_port = ostd.egress_port;
+            }
             egress_port_1 = egress_port;
             meta_1.drop = false;
             meta_1.multicast_group = 32w0;
             meta_1.egress_port = egress_port_1;
-            ostd = meta_1;
+            {
+                ostd.class_of_service = meta_1.class_of_service;
+                ostd.clone = meta_1.clone;
+                ostd.clone_session_id = meta_1.clone_session_id;
+                ostd.drop = meta_1.drop;
+                ostd.resubmit = meta_1.resubmit;
+                ostd.multicast_group = meta_1.multicast_group;
+                ostd.egress_port = meta_1.egress_port;
+            }
         }
     }
     @name("ingress.do_tst") action do_tst(PortId_t egress_port, bit<16> serEnumT) {
         {
-            meta_2 = ostd;
+            {
+                meta_2.class_of_service = ostd.class_of_service;
+                meta_2.clone = ostd.clone;
+                meta_2.clone_session_id = ostd.clone_session_id;
+                meta_2.drop = ostd.drop;
+                meta_2.resubmit = ostd.resubmit;
+                meta_2.multicast_group = ostd.multicast_group;
+                meta_2.egress_port = ostd.egress_port;
+            }
             egress_port_2 = egress_port;
             meta_2.drop = false;
             meta_2.multicast_group = 32w0;
             meta_2.egress_port = egress_port_2;
-            ostd = meta_2;
+            {
+                ostd.class_of_service = meta_2.class_of_service;
+                ostd.clone = meta_2.clone;
+                ostd.clone_session_id = meta_2.clone_session_id;
+                ostd.drop = meta_2.drop;
+                ostd.resubmit = meta_2.resubmit;
+                ostd.multicast_group = meta_2.multicast_group;
+                ostd.egress_port = meta_2.egress_port;
+            }
         }
     }
     @name("ingress.l2_tbl") table l2_tbl_0 {
