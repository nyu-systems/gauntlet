*** dumps/p4_16_samples/pipe.p4/pruned/pipe-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:00:38.930152400 +0200
--- dumps/p4_16_samples/pipe.p4/pruned/pipe-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:00:38.999734100 +0200
*************** control Q_pipe(inout TArg1 qArg1, inout
*** 62,88 ****
          const default_action = NoAction_0();
      }
      apply {
!         {
!             p1_tArg1_0.field1 = qArg1.field1;
!             p1_tArg1_0.drop = qArg1.drop;
!         }
!         {
!             p1_aArg2_0.field2 = qArg2.field2;
!         }
          p1_thost_T_0.apply();
!         {
!             qArg1.field1 = p1_tArg1_0.field1;
!         }
!         {
!             p1_tArg1_0.drop = qArg1.drop;
!         }
!         {
!             p1_aArg2_0.field2 = qArg2.field2;
!         }
          p1_thost_T_0.apply();
!         {
!             qArg1.field1 = p1_tArg1_0.field1;
!         }
          p1_Tinner_0.apply();
      }
  }
--- 62,76 ----
          const default_action = NoAction_0();
      }
      apply {
!         p1_tArg1_0.field1 = qArg1.field1;
!         p1_tArg1_0.drop = qArg1.drop;
!         p1_aArg2_0.field2 = qArg2.field2;
          p1_thost_T_0.apply();
!         qArg1.field1 = p1_tArg1_0.field1;
!         p1_tArg1_0.drop = qArg1.drop;
!         p1_aArg2_0.field2 = qArg2.field2;
          p1_thost_T_0.apply();
!         qArg1.field1 = p1_tArg1_0.field1;
          p1_Tinner_0.apply();
      }
  }
