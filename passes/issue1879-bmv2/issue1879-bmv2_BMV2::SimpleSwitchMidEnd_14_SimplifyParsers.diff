--- before_pass
+++ after_pass
@@ -88,17 +88,11 @@ parser PROTParser(packet_in packet, out
         meta_0 = meta;
         currentISelected_2 = currentISelected_0;
         currI_0 = hdr.prot_common.curri;
-        transition SubParser_start;
-    }
-    state SubParser_start {
         packet.extract<prot_i_t>(inf_0);
         subParser_currentISelected2 = currI_0 == meta_0.currPos;
         meta_0.currenti.upDirection = meta_0.currenti.upDirection + (bit<1>)subParser_currentISelected2 * inf_0.upDirection;
         meta_0.hLeft = inf_0.segLen;
         meta_0.currPos = meta_0.currPos + 8w1;
-        transition parse_prot_host_addr_src_ipv4_0;
-    }
-    state parse_prot_host_addr_src_ipv4_0 {
         hdr.prot_inf_0 = inf_0;
         meta = meta_0;
         transition parse_prot_h_0_pre;
@@ -128,17 +122,11 @@ parser PROTParser(packet_in packet, out
         meta_0 = meta;
         currentISelected_2 = currentISelected_1;
         currI_0 = hdr.prot_common.curri;
-        transition SubParser_start_0;
-    }
-    state SubParser_start_0 {
         packet.extract<prot_i_t>(inf_0);
         subParser_currentISelected2 = currI_0 == meta_0.currPos;
         meta_0.currenti.upDirection = meta_0.currenti.upDirection + (bit<1>)subParser_currentISelected2 * inf_0.upDirection;
         meta_0.hLeft = inf_0.segLen;
         meta_0.currPos = meta_0.currPos + 8w1;
-        transition parse_prot_inf;
-    }
-    state parse_prot_inf {
         hdr.prot_inf_1 = inf_0;
         meta = meta_0;
         transition accept;
