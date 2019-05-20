*** dumps/p4_16_samples/psa-counter3.p4/pruned/psa-counter3-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:00:40.513152700 +0200
--- dumps/p4_16_samples/psa-counter3.p4/pruned/psa-counter3-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-05-20 17:00:40.517758900 +0200
*************** parser MyEP(packet_in buffer, out EMPTY
*** 20,27 ****
      }
  }
  control MyIC(inout ethernet_t a, inout EMPTY b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
!     @name("MyIC.counter0") Counter<bit<10>, bit<12>>(32w1024, PSA_CounterType_t.PACKETS) counter0;
!     @name("MyIC.counter1") Counter<bit<10>, bit<12>>(32w1024, PSA_CounterType_t.PACKETS) counter1;
      apply {
          counter0.count(12w1024);
      }
--- 20,27 ----
      }
  }
  control MyIC(inout ethernet_t a, inout EMPTY b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
!     @name("MyIC.counter0") Counter<bit<10>, bit<12>>(32w1024, 32w0) counter0;
!     @name("MyIC.counter1") Counter<bit<10>, bit<12>>(32w1024, 32w0) counter1;
      apply {
          counter0.count(12w1024);
      }
