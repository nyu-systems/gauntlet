--- before_pass
+++ after_pass
@@ -134,6 +134,7 @@ parser FabricParser(packet_in packet, ou
     }
 }
 control FabricIngress(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
+    PortId_t forwarding_mask_0;
     @name(".drop") action drop() {
         mark_to_drop();
     }
@@ -157,7 +158,6 @@ control FabricIngress(inout parsed_heade
         }
         default_action = NoAction_0();
     }
-    PortId_t forwarding_mask_0;
     @name("FabricIngress.forwarding.fwd") action forwarding_fwd(PortId_t next_port) {
         standard_metadata.egress_spec = next_port;
     }
