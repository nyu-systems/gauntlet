*** dumps/p4_16_samples/serenum.p4/pruned/serenum-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:00:20.832211000 +0200
--- dumps/p4_16_samples/serenum.p4/pruned/serenum-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:00:20.861161200 +0200
*************** parser prs(packet_in p, out Headers h) {
*** 19,26 ****
      }
  }
  control c(inout Headers h) {
      apply {
!         bool hasReturned_0 = false;
          if (!h.eth.isValid()) 
              hasReturned_0 = true;
          if (!hasReturned_0) 
--- 19,27 ----
      }
  }
  control c(inout Headers h) {
+     bool hasReturned_0;
      apply {
!         hasReturned_0 = false;
          if (!h.eth.isValid()) 
              hasReturned_0 = true;
          if (!hasReturned_0) 
