*** dumps/p4_16_samples/std_meta_inlining.p4/pruned/std_meta_inlining-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:00:32.505565600 +0200
--- dumps/p4_16_samples/std_meta_inlining.p4/pruned/std_meta_inlining-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:00:32.479369900 +0200
*************** control DeparserImpl(packet_out packet,
*** 14,21 ****
      }
  }
  control ingress(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
!     @name(".send_to_cpu") action send_to_cpu(inout standard_metadata_t standard_metadata_1) {
          standard_metadata_1.egress_spec = 9w64;
      }
      @name(".NoAction") action NoAction_0() {
      }
--- 14,24 ----
      }
  }
  control ingress(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
!     standard_metadata_t standard_metadata_1;
!     @name(".send_to_cpu") action send_to_cpu() {
!         standard_metadata_1 = standard_metadata;
          standard_metadata_1.egress_spec = 9w64;
+         standard_metadata = standard_metadata_1;
      }
      @name(".NoAction") action NoAction_0() {
      }
*************** control ingress(inout headers_t hdr, ino
*** 24,30 ****
              standard_metadata.ingress_port: ternary @name("standard_metadata.ingress_port") ;
          }
          actions = {
!             send_to_cpu(standard_metadata);
              @defaultonly NoAction_0();
          }
          default_action = NoAction_0();
--- 27,33 ----
              standard_metadata.ingress_port: ternary @name("standard_metadata.ingress_port") ;
          }
          actions = {
!             send_to_cpu();
              @defaultonly NoAction_0();
          }
          default_action = NoAction_0();
