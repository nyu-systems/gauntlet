--- before_pass
+++ after_pass
@@ -37,29 +37,20 @@ match_kind {
     @alias("intrinsic_metadata.recirculate_flag") 
     bit<32>  recirculate_flag;
 }
-enum CounterType {
-    packets,
-    bytes,
-    packets_and_bytes
-}
-enum MeterType {
-    packets,
-    bytes
-}
 extern counter {
-    counter(bit<32> size, CounterType type);
+    counter(bit<32> size, bit<32> type);
     void count(in bit<32> index);
 }
 extern direct_counter {
-    direct_counter(CounterType type);
+    direct_counter(bit<32> type);
     void count();
 }
 extern meter {
-    meter(bit<32> size, MeterType type);
+    meter(bit<32> size, bit<32> type);
     void execute_meter<T>(in bit<32> index, out T result);
 }
 extern direct_meter<T> {
-    direct_meter(MeterType type);
+    direct_meter(bit<32> type);
     void read(out T result);
 }
 extern register<T> {
@@ -70,19 +61,9 @@ extern register<T> {
 extern action_profile {
     action_profile(bit<32> size);
 }
-enum HashAlgorithm {
-    crc32,
-    crc32_custom,
-    crc16,
-    crc16_custom,
-    random,
-    identity,
-    csum16,
-    xor16
-}
 extern void mark_to_drop();
 extern action_selector {
-    action_selector(HashAlgorithm algorithm, bit<32> size, bit<32> outputWidth);
+    action_selector(bit<32> algorithm, bit<32> size, bit<32> outputWidth);
 }
 @deprecated("Please use verify_checksum/update_checksum instead.") extern Checksum16 {
     Checksum16();
