*** dumps/p4_16_samples/issue1781-bmv2.p4/pruned/issue1781-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:57.398780400 +0200
--- dumps/p4_16_samples/issue1781-bmv2.p4/pruned/issue1781-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:57.401581500 +0200
*************** parser ParserImpl(packet_in packet, out
*** 10,41 ****
      }
  }
  bit<32> test_func() {
!     bool hasReturned_0;
!     bit<32> retval_0;
!     hasReturned_0 = false;
!     hasReturned_0 = true;
!     retval_0 = 32w1;
!     return retval_0;
  }
  control IngressImpl(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
-     bit<32> value_2;
-     bit<32> tmp_1;
-     bit<32> tmp_2;
-     bool hasReturned_1;
-     bit<32> retval_1;
-     bit<32> value_0;
      @name("IngressImpl.update_value") action update_value_0() {
          {
-             hasReturned_1 = false;
-             hasReturned_1 = true;
-             retval_1 = 32w1;
-             tmp_1 = retval_1;
          }
-         value_0 = tmp_1;
-         value_2 = value_0;
      }
      apply {
!         tmp_2 = test_func();
          update_value_0();
      }
  }
--- 10,24 ----
      }
  }
  bit<32> test_func() {
!     return 32w1;
  }
  control IngressImpl(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
      @name("IngressImpl.update_value") action update_value_0() {
          {
          }
      }
      apply {
!         test_func();
          update_value_0();
      }
  }
