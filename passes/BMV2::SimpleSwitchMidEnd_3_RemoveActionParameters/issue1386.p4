*** dumps/p4_16_samples/issue1386.p4/pruned/issue1386-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:58:44.129659100 +0200
--- dumps/p4_16_samples/issue1386.p4/pruned/issue1386-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:58:44.100195600 +0200
*************** control deparser(packet_out b, in Header
*** 33,41 ****
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
      bit<8> c_n_0;
      apply {
          {
!             bool c_hasReturned_0 = false;
              c_n_0 = 8w0;
              if (!h.h.isValid()) 
                  c_hasReturned_0 = true;
--- 33,42 ----
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
      bit<8> c_n_0;
+     bool c_hasReturned_0;
      apply {
          {
!             c_hasReturned_0 = false;
              c_n_0 = 8w0;
              if (!h.h.isValid()) 
                  c_hasReturned_0 = true;
