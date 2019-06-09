--- before_pass
+++ after_pass
@@ -47,19 +47,19 @@ enum MeterType {
     bytes
 }
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
@@ -82,7 +82,7 @@ enum HashAlgorithm {
 }
 extern void mark_to_drop();
 extern action_selector {
-    action_selector(HashAlgorithm algorithm, bit<32> size, bit<32> outputWidth);
+    action_selector(bit<32> algorithm, bit<32> size, bit<32> outputWidth);
 }
 @deprecated("Please use verify_checksum/update_checksum instead.") extern Checksum16 {
     Checksum16();
