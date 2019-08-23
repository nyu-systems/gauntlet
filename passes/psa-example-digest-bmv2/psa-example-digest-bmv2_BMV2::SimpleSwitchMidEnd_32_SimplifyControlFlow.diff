--- before_pass
+++ after_pass
@@ -95,22 +95,14 @@ control ingress(inout headers hdr, inout
         default_action = unknown_source();
     }
     @name("ingress.do_L2_forward") action do_L2_forward(PortId_t egress_port) {
-        {
-            {
-                ostd.drop = false;
-                ostd.multicast_group = 32w0;
-                ostd.egress_port = egress_port;
-            }
-        }
+        ostd.drop = false;
+        ostd.multicast_group = 32w0;
+        ostd.egress_port = egress_port;
     }
     @name("ingress.do_tst") action do_tst(PortId_t egress_port, bit<16> serEnumT) {
-        {
-            {
-                ostd.drop = false;
-                ostd.multicast_group = 32w0;
-                ostd.egress_port = egress_port;
-            }
-        }
+        ostd.drop = false;
+        ostd.multicast_group = 32w0;
+        ostd.egress_port = egress_port;
     }
     @name("ingress.l2_tbl") table l2_tbl_0 {
         key = {
