*** dumps/p4_16_samples/issue1386.p4/pruned/issue1386-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:44.057019200 +0200
--- dumps/p4_16_samples/issue1386.p4/pruned/issue1386-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:44.059889100 +0200
*************** control deparser(packet_out b, in Header
*** 32,47 ****
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
-     bit<8> c_n_0;
      bool c_hasReturned_0;
      apply {
          {
              c_hasReturned_0 = false;
-             c_n_0 = 8w0;
              if (!h.h.isValid()) 
                  c_hasReturned_0 = true;
              if (!c_hasReturned_0) 
!                 if (c_n_0 > 8w0) 
                      h.h.setValid();
          }
          sm.egress_spec = 9w0;
--- 32,45 ----
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
      bool c_hasReturned_0;
      apply {
          {
              c_hasReturned_0 = false;
              if (!h.h.isValid()) 
                  c_hasReturned_0 = true;
              if (!c_hasReturned_0) 
!                 if (8w0 > 8w0) 
                      h.h.setValid();
          }
          sm.egress_spec = 9w0;
