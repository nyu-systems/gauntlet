*** dumps/p4_16_samples/psa-counter1.p4/pruned/psa-counter1-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:00:01.340383200 +0200
--- dumps/p4_16_samples/psa-counter1.p4/pruned/psa-counter1-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-05-20 17:00:01.344579800 +0200
*************** parser MyEP(packet_in buffer, out EMPTY
*** 24,30 ****
  control MyIC(inout ethernet_t a, inout EMPTY b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
      @name(".NoAction") action NoAction_0() {
      }
!     @name("MyIC.counter") Counter<bit<10>, bit<12>>(32w1024, PSA_CounterType_t.PACKETS) counter;
      @name("MyIC.execute") action execute_0() {
          counter.count(12w1024);
      }
--- 24,30 ----
  control MyIC(inout ethernet_t a, inout EMPTY b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
      @name(".NoAction") action NoAction_0() {
      }
!     @name("MyIC.counter") Counter<bit<10>, bit<12>>(32w1024, 32w0) counter;
      @name("MyIC.execute") action execute_0() {
          counter.count(12w1024);
      }
