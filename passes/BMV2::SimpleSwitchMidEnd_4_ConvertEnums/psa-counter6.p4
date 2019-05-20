*** dumps/p4_16_samples/psa-counter6.p4/pruned/psa-counter6-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:00:03.148385500 +0200
--- dumps/p4_16_samples/psa-counter6.p4/pruned/psa-counter6-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-05-20 17:00:03.151740300 +0200
*************** control MyIC(inout ethernet_t a, inout E
*** 24,30 ****
      }
      @name(".NoAction") action NoAction_3() {
      }
!     @name("MyIC.counter0") DirectCounter<bit<12>>(PSA_CounterType_t.PACKETS) counter0;
      @name("MyIC.execute") action execute_0() {
          counter0.count();
      }
--- 24,30 ----
      }
      @name(".NoAction") action NoAction_3() {
      }
!     @name("MyIC.counter0") DirectCounter<bit<12>>(32w0) counter0;
      @name("MyIC.execute") action execute_0() {
          counter0.count();
      }
