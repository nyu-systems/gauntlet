*** dumps/p4_16_samples/psa-portid-using-newtype2.p4/pruned/psa-portid-using-newtype2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:00:15.580834800 +0200
--- dumps/p4_16_samples/psa-portid-using-newtype2.p4/pruned/psa-portid-using-newtype2-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-05-20 17:00:15.583116300 +0200
*************** match_kind {
*** 37,65 ****
      @alias("intrinsic_metadata.recirculate_flag") 
      bit<32>  recirculate_flag;
  }
- enum CounterType {
-     packets,
-     bytes,
-     packets_and_bytes
- }
- enum MeterType {
-     packets,
-     bytes
- }
  extern counter {
!     counter(bit<32> size, CounterType type);
      void count(in bit<32> index);
  }
  extern direct_counter {
!     direct_counter(CounterType type);
      void count();
  }
  extern meter {
!     meter(bit<32> size, MeterType type);
      void execute_meter<T>(in bit<32> index, out T result);
  }
  extern direct_meter<T> {
!     direct_meter(MeterType type);
      void read(out T result);
  }
  extern register<T> {
--- 37,56 ----
      @alias("intrinsic_metadata.recirculate_flag") 
      bit<32>  recirculate_flag;
  }
  extern counter {
!     counter(bit<32> size, bit<32> type);
      void count(in bit<32> index);
  }
  extern direct_counter {
!     direct_counter(bit<32> type);
      void count();
  }
  extern meter {
!     meter(bit<32> size, bit<32> type);
      void execute_meter<T>(in bit<32> index, out T result);
  }
  extern direct_meter<T> {
!     direct_meter(bit<32> type);
      void read(out T result);
  }
  extern register<T> {
*************** extern register<T> {
*** 70,88 ****
  extern action_profile {
      action_profile(bit<32> size);
  }
- enum HashAlgorithm {
-     crc32,
-     crc32_custom,
-     crc16,
-     crc16_custom,
-     random,
-     identity,
-     csum16,
-     xor16
- }
  extern void mark_to_drop();
  extern action_selector {
!     action_selector(HashAlgorithm algorithm, bit<32> size, bit<32> outputWidth);
  }
  @deprecated("Please use verify_checksum/update_checksum instead.") extern Checksum16 {
      Checksum16();
--- 61,69 ----
  extern action_profile {
      action_profile(bit<32> size);
  }
  extern void mark_to_drop();
  extern action_selector {
!     action_selector(bit<32> algorithm, bit<32> size, bit<32> outputWidth);
  }
  @deprecated("Please use verify_checksum/update_checksum instead.") extern Checksum16 {
      Checksum16();
