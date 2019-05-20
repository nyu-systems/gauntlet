*** dumps/p4_16_samples/psa-counter4.p4/pruned/psa-counter4-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:00:02.533788500 +0200
--- dumps/p4_16_samples/psa-counter4.p4/pruned/psa-counter4-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-05-20 17:00:02.536264300 +0200
*************** parser MyEP(packet_in buffer, out EMPTY
*** 22,28 ****
  control MyIC(inout ethernet_t a, inout EMPTY b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
      @name(".NoAction") action NoAction_0() {
      }
!     @name("MyIC.counter0") DirectCounter<bit<12>>(PSA_CounterType_t.PACKETS) counter0;
      @name("MyIC.tbl") table tbl {
          key = {
              a.srcAddr: exact @name("a.srcAddr") ;
--- 22,28 ----
  control MyIC(inout ethernet_t a, inout EMPTY b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
      @name(".NoAction") action NoAction_0() {
      }
!     @name("MyIC.counter0") DirectCounter<bit<12>>(32w0) counter0;
      @name("MyIC.tbl") table tbl {
          key = {
              a.srcAddr: exact @name("a.srcAddr") ;
