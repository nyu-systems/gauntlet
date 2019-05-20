*** dumps/p4_16_samples/psa-portid-using-newtype2.p4/pruned/psa-portid-using-newtype2-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:00:15.529454400 +0200
--- dumps/p4_16_samples/psa-portid-using-newtype2.p4/pruned/psa-portid-using-newtype2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:00:15.580834800 +0200
*************** parser FabricParser(packet_in packet, ou
*** 134,139 ****
--- 134,140 ----
      }
  }
  control FabricIngress(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
+     PortId_t forwarding_mask_0;
      @name(".drop") action drop() {
          mark_to_drop();
      }
*************** control FabricIngress(inout parsed_heade
*** 157,163 ****
          }
          default_action = NoAction_0();
      }
-     PortId_t forwarding_mask_0;
      @name("FabricIngress.forwarding.fwd") action forwarding_fwd(PortId_t next_port) {
          standard_metadata.egress_spec = next_port;
      }
--- 158,163 ----
