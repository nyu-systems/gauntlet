*** dumps/p4_16_samples/issue1386.p4/pruned/issue1386-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:58:44.072553400 +0200
--- dumps/p4_16_samples/issue1386.p4/pruned/issue1386-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:58:44.075483600 +0200
*************** control deparser(packet_out b, in Header
*** 34,46 ****
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
      bool c_hasReturned_0;
      apply {
!         {
!             c_hasReturned_0 = false;
!             if (!h.h.isValid()) 
!                 c_hasReturned_0 = true;
!             if (!c_hasReturned_0) 
!                 ;
!         }
          sm.egress_spec = 9w0;
      }
  }
--- 34,42 ----
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
      bool c_hasReturned_0;
      apply {
!         c_hasReturned_0 = false;
!         if (!h.h.isValid()) 
!             c_hasReturned_0 = true;
          sm.egress_spec = 9w0;
      }
  }
