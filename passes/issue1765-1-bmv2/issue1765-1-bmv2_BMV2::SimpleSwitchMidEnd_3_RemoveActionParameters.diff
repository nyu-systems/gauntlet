--- before_pass
+++ after_pass
@@ -161,14 +161,14 @@ control MyComputeChecksum(inout headers
     }
 }
 control MyIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
+    mac_addr_t mac_tmp_0;
+    ipv6_addr_t addr_tmp_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name(".NoAction") action NoAction_4() {
     }
     @name(".NoAction") action NoAction_5() {
     }
-    mac_addr_t mac_tmp_0;
-    ipv6_addr_t addr_tmp_0;
     @name("MyIngress.set_egress_port") action set_egress_port(port_t out_port) {
         standard_metadata.egress_spec = out_port;
     }
