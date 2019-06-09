--- before_pass
+++ after_pass
@@ -154,7 +154,7 @@ control ingress(inout headers hdr, inout
         flowlet_id_0.read(meta._ingress_metadata_flowlet_id2, (bit<32>)meta._ingress_metadata_flowlet_map_index1);
         meta._ingress_metadata_flow_ipg0 = (bit<32>)standard_metadata.ingress_global_timestamp;
         flowlet_lasttime_0.read(meta._ingress_metadata_flowlet_lasttime3, (bit<32>)meta._ingress_metadata_flowlet_map_index1);
-        meta._ingress_metadata_flow_ipg0 = meta._ingress_metadata_flow_ipg0 - meta._ingress_metadata_flowlet_lasttime3;
+        meta._ingress_metadata_flow_ipg0 = (bit<32>)standard_metadata.ingress_global_timestamp - meta._ingress_metadata_flowlet_lasttime3;
         flowlet_lasttime_0.write((bit<32>)meta._ingress_metadata_flowlet_map_index1, (bit<32>)standard_metadata.ingress_global_timestamp);
     }
     @name("ingress.set_dmac") action set_dmac(bit<48> dmac) {
