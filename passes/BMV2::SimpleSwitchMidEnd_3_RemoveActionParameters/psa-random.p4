*** dumps/p4_16_samples/psa-random.p4/pruned/psa-random-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:00:16.263902400 +0200
--- dumps/p4_16_samples/psa-random.p4/pruned/psa-random-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:00:16.232632900 +0200
*************** parser MyEP(packet_in buffer, out EMPTY
*** 23,31 ****
      }
  }
  control MyIC(inout ethernet_t a, inout user_meta_t b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
      @name(".NoAction") action NoAction_0() {
      }
-     bit<16> tmp_0;
      @name("MyIC.rand") Random<bit<16>>(16w200, 16w400) rand;
      @name("MyIC.execute_random") action execute_random_0() {
          tmp_0 = rand.read();
--- 23,31 ----
      }
  }
  control MyIC(inout ethernet_t a, inout user_meta_t b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
+     bit<16> tmp_0;
      @name(".NoAction") action NoAction_0() {
      }
      @name("MyIC.rand") Random<bit<16>>(16w200, 16w400) rand;
      @name("MyIC.execute_random") action execute_random_0() {
          tmp_0 = rand.read();
